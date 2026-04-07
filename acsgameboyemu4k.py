#!/usr/bin/env python3
"""
Cat's Gameboy Emu 1.x
A minimalist Game Boy emulator in a single Python file.
GUI: tkinter with black background and blue text.
Requires: Python 3.10+ (tested on 3.14)
"""

import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import threading
import time
import sys
import os
from array import array
from collections import deque
import struct

# ----------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------
SCREEN_W = 160
SCREEN_H = 144
SCALE = 3  # window scale factor

# Game Boy CPU frequency (approx 4.19 MHz) but we'll run frame-based
CYCLES_PER_FRAME = 70224  # ~59.7 Hz

# ----------------------------------------------------------------------
# Memory Management Unit (MMU)
# ----------------------------------------------------------------------
class MMU:
    def __init__(self):
        self.rom = bytearray(0x8000)      # 32KB ROM bank 0
        self.vram = bytearray(0x2000)     # 8KB Video RAM
        self.eram = bytearray(0x2000)     # 8KB External RAM
        self.wram = bytearray(0x2000)     # 8KB Work RAM
        self.oam = bytearray(0xA0)        # Sprite attribute table
        self.io = bytearray(0x80)         # I/O registers
        self.hram = bytearray(0x7F)       # High RAM
        self.ie = 0                       # Interrupt enable
        self.rom_bank = [bytearray(0x4000)]  # MBC0: only bank 0
        self.mbc_mode = 0
        self.ram_enable = False
        self.cart_ram = bytearray(0)      # no cartridge RAM for MBC0

        # Initial values for some I/O registers
        self.io[0x40] = 0x91  # LCDC: LCD enabled, BG tile map $9800, etc.

    def load_rom(self, rom_data):
        if len(rom_data) < 0x8000:
            self.rom[:len(rom_data)] = rom_data
        else:
            self.rom = rom_data[:0x8000]
        # Determine MBC type from header at $0147
        if len(rom_data) > 0x147:
            mbc = rom_data[0x147]
            if mbc == 0:
                self.mbc_mode = 0
            # else: we only support MBC0 for simplicity

    def read(self, addr):
        # ROM bank 0
        if 0x0000 <= addr < 0x4000:
            return self.rom[addr]
        # ROM bank 1 (switchable, but we only have bank 0 for MBC0)
        elif 0x4000 <= addr < 0x8000:
            return self.rom[addr]  # in MBC0, it's just the same ROM
        # VRAM
        elif 0x8000 <= addr < 0xA000:
            return self.vram[addr - 0x8000]
        # External RAM
        elif 0xA000 <= addr < 0xC000:
            if self.ram_enable:
                if addr - 0xA000 < len(self.cart_ram):
                    return self.cart_ram[addr - 0xA000]
                return 0xFF
            return 0xFF
        # Work RAM
        elif 0xC000 <= addr < 0xE000:
            return self.wram[addr - 0xC000]
        # Echo RAM (mirror of C000-DDFF)
        elif 0xE000 <= addr < 0xFE00:
            return self.wram[addr - 0xE000]
        # OAM
        elif 0xFE00 <= addr < 0xFEA0:
            return self.oam[addr - 0xFE00]
        # Unusable
        elif 0xFEA0 <= addr < 0xFF00:
            return 0
        # I/O Registers
        elif 0xFF00 <= addr < 0xFF80:
            return self.io[addr - 0xFF00]
        # HRAM
        elif 0xFF80 <= addr < 0xFFFF:
            return self.hram[addr - 0xFF80]
        # IE
        elif addr == 0xFFFF:
            return self.ie
        return 0xFF

    def write(self, addr, value):
        value &= 0xFF
        # ROM area: MBC control (ignored for MBC0)
        if 0x0000 <= addr < 0x8000:
            # MBC control: RAM enable and ROM bank select
            if addr < 0x2000:
                self.ram_enable = (value & 0x0F) == 0x0A
            return
        # VRAM
        elif 0x8000 <= addr < 0xA000:
            self.vram[addr - 0x8000] = value
        # External RAM
        elif 0xA000 <= addr < 0xC000:
            if self.ram_enable:
                if addr - 0xA000 < len(self.cart_ram):
                    self.cart_ram[addr - 0xA000] = value
        # Work RAM
        elif 0xC000 <= addr < 0xE000:
            self.wram[addr - 0xC000] = value
        # Echo RAM
        elif 0xE000 <= addr < 0xFE00:
            self.wram[addr - 0xE000] = value
        # OAM
        elif 0xFE00 <= addr < 0xFEA0:
            self.oam[addr - 0xFE00] = value
        # I/O Registers
        elif 0xFF00 <= addr < 0xFF80:
            offset = addr - 0xFF00
            # Joypad register (0xFF00)
            if offset == 0x00:
                # Only bits 4-5 are writable; lower bits are input from joypad
                self.io[0] = (value & 0x30) | (self.io[0] & 0x0F)
            # Divider register (0xFF04) - writing resets it
            elif offset == 0x04:
                self.io[4] = 0
            # LCDC (0xFF40)
            elif offset == 0x40:
                self.io[0x40] = value
            # DMA transfer (0xFF46)
            elif offset == 0x46:
                self._dma_transfer(value)
            else:
                self.io[offset] = value
        # HRAM
        elif 0xFF80 <= addr < 0xFFFF:
            self.hram[addr - 0xFF80] = value
        # IE
        elif addr == 0xFFFF:
            self.ie = value

    def _dma_transfer(self, value):
        """DMA transfer from address (value << 8) to OAM."""
        src = (value << 8) & 0xFFFF
        for i in range(0xA0):
            self.oam[i] = self.read(src + i)

# ----------------------------------------------------------------------
# CPU (LR35902)
# ----------------------------------------------------------------------
class CPU:
    def __init__(self, mmu):
        self.mmu = mmu
        self.reset()

    def reset(self):
        # Registers
        self.a = 0x01
        self.f = 0xB0  # Z=0, N=0, H=0, C=0 (flags)
        self.b = 0x00
        self.c = 0x13
        self.d = 0x00
        self.e = 0xD8
        self.h = 0x01
        self.l = 0x4D
        self.sp = 0xFFFE
        self.pc = 0x0100

        self.ime = True   # interrupt master enable (simplified)
        self.halt = False
        self.stop = False
        self.cycles = 0

    # Flag helpers
    @property
    def _z(self): return (self.f >> 7) & 1
    @_z.setter
    def _z(self, v): self.f = (self.f & 0x7F) | ((v & 1) << 7)

    @property
    def _n(self): return (self.f >> 6) & 1
    @_n.setter
    def _n(self, v): self.f = (self.f & 0xBF) | ((v & 1) << 6)

    @property
    def _h(self): return (self.f >> 5) & 1
    @_h.setter
    def _h(self, v): self.f = (self.f & 0xDF) | ((v & 1) << 5)

    @property
    def _c(self): return (self.f >> 4) & 1
    @_c.setter
    def _c(self, v): self.f = (self.f & 0xEF) | ((v & 1) << 4)

    # Combined registers
    @property
    def af(self): return (self.a << 8) | self.f
    @af.setter
    def af(self, v):
        self.a = (v >> 8) & 0xFF
        self.f = v & 0xF0  # lower 4 bits always 0

    @property
    def bc(self): return (self.b << 8) | self.c
    @bc.setter
    def bc(self, v):
        self.b = (v >> 8) & 0xFF
        self.c = v & 0xFF

    @property
    def de(self): return (self.d << 8) | self.e
    @de.setter
    def de(self, v):
        self.d = (v >> 8) & 0xFF
        self.e = v & 0xFF

    @property
    def hl(self): return (self.h << 8) | self.l
    @hl.setter
    def hl(self, v):
        self.h = (v >> 8) & 0xFF
        self.l = v & 0xFF

    # Memory access helpers
    def read8(self, addr):
        return self.mmu.read(addr)

    def write8(self, addr, value):
        self.mmu.write(addr, value & 0xFF)

    def read16(self, addr):
        lo = self.read8(addr)
        hi = self.read8(addr + 1)
        return (hi << 8) | lo

    def write16(self, addr, value):
        self.write8(addr, value & 0xFF)
        self.write8(addr + 1, (value >> 8) & 0xFF)

    def fetch8(self):
        val = self.read8(self.pc)
        self.pc = (self.pc + 1) & 0xFFFF
        return val

    def fetch16(self):
        lo = self.fetch8()
        hi = self.fetch8()
        return (hi << 8) | lo

    def push16(self, value):
        self.sp = (self.sp - 1) & 0xFFFF
        self.write8(self.sp, (value >> 8) & 0xFF)
        self.sp = (self.sp - 1) & 0xFFFF
        self.write8(self.sp, value & 0xFF)

    def pop16(self):
        lo = self.read8(self.sp)
        self.sp = (self.sp + 1) & 0xFFFF
        hi = self.read8(self.sp)
        self.sp = (self.sp + 1) & 0xFFFF
        return (hi << 8) | lo

    def step(self):
        """Execute one instruction, return cycles taken."""
        if self.halt:
            return 4  # HALT mode

        op = self.fetch8()
        # Prefix CB
        if op == 0xCB:
            op = self.fetch8()
            return self._exec_cb(op)
        else:
            return self._exec_op(op)

    def _exec_op(self, op):
        # This is a minimal instruction set – enough for simple ROMs.
        # Many instructions are missing for brevity but this core works for basic demos.
        if op == 0x00:  # NOP
            return 4
        elif op == 0x01:  # LD BC, d16
            self.bc = self.fetch16()
            return 12
        elif op == 0x02:  # LD (BC), A
            self.write8(self.bc, self.a)
            return 8
        elif op == 0x03:  # INC BC
            self.bc = (self.bc + 1) & 0xFFFF
            return 8
        elif op == 0x04:  # INC B
            self._h = ((self.b & 0x0F) + 1) > 0x0F
            self.b = (self.b + 1) & 0xFF
            self._z = self.b == 0
            self._n = 0
            return 4
        elif op == 0x05:  # DEC B
            self._h = (self.b & 0x0F) == 0
            self.b = (self.b - 1) & 0xFF
            self._z = self.b == 0
            self._n = 1
            return 4
        elif op == 0x06:  # LD B, d8
            self.b = self.fetch8()
            return 8
        elif op == 0x07:  # RLCA
            carry = (self.a >> 7) & 1
            self.a = ((self.a << 1) | carry) & 0xFF
            self._c = carry
            self._z = self._n = self._h = 0
            return 4
        elif op == 0x08:  # LD (a16), SP
            addr = self.fetch16()
            self.write16(addr, self.sp)
            return 20
        elif op == 0x09:  # ADD HL, BC
            hl = self.hl
            bc = self.bc
            result = hl + bc
            self._n = 0
            self._h = ((hl & 0xFFF) + (bc & 0xFFF)) > 0xFFF
            self._c = result > 0xFFFF
            self.hl = result & 0xFFFF
            return 8
        elif op == 0x0A:  # LD A, (BC)
            self.a = self.read8(self.bc)
            return 8
        elif op == 0x0B:  # DEC BC
            self.bc = (self.bc - 1) & 0xFFFF
            return 8
        elif op == 0x0C:  # INC C
            self._h = ((self.c & 0x0F) + 1) > 0x0F
            self.c = (self.c + 1) & 0xFF
            self._z = self.c == 0
            self._n = 0
            return 4
        elif op == 0x0D:  # DEC C
            self._h = (self.c & 0x0F) == 0
            self.c = (self.c - 1) & 0xFF
            self._z = self.c == 0
            self._n = 1
            return 4
        elif op == 0x0E:  # LD C, d8
            self.c = self.fetch8()
            return 8
        elif op == 0x0F:  # RRCA
            carry = self.a & 1
            self.a = ((self.a >> 1) | (carry << 7)) & 0xFF
            self._c = carry
            self._z = self._n = self._h = 0
            return 4
        # Stop (0x10) - ignore
        elif op == 0x10:
            self.stop = True
            return 4
        elif op == 0x11:  # LD DE, d16
            self.de = self.fetch16()
            return 12
        elif op == 0x12:  # LD (DE), A
            self.write8(self.de, self.a)
            return 8
        elif op == 0x13:  # INC DE
            self.de = (self.de + 1) & 0xFFFF
            return 8
        elif op == 0x14:  # INC D
            self._h = ((self.d & 0x0F) + 1) > 0x0F
            self.d = (self.d + 1) & 0xFF
            self._z = self.d == 0
            self._n = 0
            return 4
        elif op == 0x15:  # DEC D
            self._h = (self.d & 0x0F) == 0
            self.d = (self.d - 1) & 0xFF
            self._z = self.d == 0
            self._n = 1
            return 4
        elif op == 0x16:  # LD D, d8
            self.d = self.fetch8()
            return 8
        elif op == 0x17:  # RLA
            carry = self._c
            self._c = (self.a >> 7) & 1
            self.a = ((self.a << 1) | carry) & 0xFF
            self._z = self._n = self._h = 0
            return 4
        elif op == 0x18:  # JR e
            offset = self.fetch8()
            if offset & 0x80:
                offset = -((~offset + 1) & 0xFF)
            self.pc = (self.pc + offset) & 0xFFFF
            return 12
        elif op == 0x19:  # ADD HL, DE
            hl = self.hl
            de = self.de
            result = hl + de
            self._n = 0
            self._h = ((hl & 0xFFF) + (de & 0xFFF)) > 0xFFF
            self._c = result > 0xFFFF
            self.hl = result & 0xFFFF
            return 8
        elif op == 0x1A:  # LD A, (DE)
            self.a = self.read8(self.de)
            return 8
        elif op == 0x1B:  # DEC DE
            self.de = (self.de - 1) & 0xFFFF
            return 8
        elif op == 0x1C:  # INC E
            self._h = ((self.e & 0x0F) + 1) > 0x0F
            self.e = (self.e + 1) & 0xFF
            self._z = self.e == 0
            self._n = 0
            return 4
        elif op == 0x1D:  # DEC E
            self._h = (self.e & 0x0F) == 0
            self.e = (self.e - 1) & 0xFF
            self._z = self.e == 0
            self._n = 1
            return 4
        elif op == 0x1E:  # LD E, d8
            self.e = self.fetch8()
            return 8
        elif op == 0x1F:  # RRA
            carry = self._c
            self._c = self.a & 1
            self.a = ((self.a >> 1) | (carry << 7)) & 0xFF
            self._z = self._n = self._h = 0
            return 4
        elif op == 0x20:  # JR NZ, e
            offset = self.fetch8()
            if not self._z:
                if offset & 0x80:
                    offset = -((~offset + 1) & 0xFF)
                self.pc = (self.pc + offset) & 0xFFFF
                return 12
            return 8
        elif op == 0x21:  # LD HL, d16
            self.hl = self.fetch16()
            return 12
        elif op == 0x22:  # LD (HL+), A
            self.write8(self.hl, self.a)
            self.hl = (self.hl + 1) & 0xFFFF
            return 8
        elif op == 0x23:  # INC HL
            self.hl = (self.hl + 1) & 0xFFFF
            return 8
        elif op == 0x24:  # INC H
            self._h = ((self.h & 0x0F) + 1) > 0x0F
            self.h = (self.h + 1) & 0xFF
            self._z = self.h == 0
            self._n = 0
            return 4
        elif op == 0x25:  # DEC H
            self._h = (self.h & 0x0F) == 0
            self.h = (self.h - 1) & 0xFF
            self._z = self.h == 0
            self._n = 1
            return 4
        elif op == 0x26:  # LD H, d8
            self.h = self.fetch8()
            return 8
        elif op == 0x27:  # DAA (simplified)
            # Decimal adjust A for BCD arithmetic
            if not self._n:
                if self._c or self.a > 0x99:
                    self.a = (self.a + 0x60) & 0xFF
                    self._c = 1
                if self._h or (self.a & 0x0F) > 0x09:
                    self.a = (self.a + 0x06) & 0xFF
            else:
                if self._c:
                    self.a = (self.a - 0x60) & 0xFF
                if self._h:
                    self.a = (self.a - 0x06) & 0xFF
            self._z = self.a == 0
            self._h = 0
            return 4
        elif op == 0x28:  # JR Z, e
            offset = self.fetch8()
            if self._z:
                if offset & 0x80:
                    offset = -((~offset + 1) & 0xFF)
                self.pc = (self.pc + offset) & 0xFFFF
                return 12
            return 8
        elif op == 0x29:  # ADD HL, HL
            hl = self.hl
            result = hl + hl
            self._n = 0
            self._h = ((hl & 0xFFF) + (hl & 0xFFF)) > 0xFFF
            self._c = result > 0xFFFF
            self.hl = result & 0xFFFF
            return 8
        elif op == 0x2A:  # LD A, (HL+)
            self.a = self.read8(self.hl)
            self.hl = (self.hl + 1) & 0xFFFF
            return 8
        elif op == 0x2B:  # DEC HL
            self.hl = (self.hl - 1) & 0xFFFF
            return 8
        elif op == 0x2C:  # INC L
            self._h = ((self.l & 0x0F) + 1) > 0x0F
            self.l = (self.l + 1) & 0xFF
            self._z = self.l == 0
            self._n = 0
            return 4
        elif op == 0x2D:  # DEC L
            self._h = (self.l & 0x0F) == 0
            self.l = (self.l - 1) & 0xFF
            self._z = self.l == 0
            self._n = 1
            return 4
        elif op == 0x2E:  # LD L, d8
            self.l = self.fetch8()
            return 8
        elif op == 0x2F:  # CPL
            self.a ^= 0xFF
            self._n = 1
            self._h = 1
            return 4
        elif op == 0x30:  # JR NC, e
            offset = self.fetch8()
            if not self._c:
                if offset & 0x80:
                    offset = -((~offset + 1) & 0xFF)
                self.pc = (self.pc + offset) & 0xFFFF
                return 12
            return 8
        elif op == 0x31:  # LD SP, d16
            self.sp = self.fetch16()
            return 12
        elif op == 0x32:  # LD (HL-), A
            self.write8(self.hl, self.a)
            self.hl = (self.hl - 1) & 0xFFFF
            return 8
        elif op == 0x33:  # INC SP
            self.sp = (self.sp + 1) & 0xFFFF
            return 8
        elif op == 0x34:  # INC (HL)
            val = self.read8(self.hl)
            self._h = ((val & 0x0F) + 1) > 0x0F
            val = (val + 1) & 0xFF
            self.write8(self.hl, val)
            self._z = val == 0
            self._n = 0
            return 12
        elif op == 0x35:  # DEC (HL)
            val = self.read8(self.hl)
            self._h = (val & 0x0F) == 0
            val = (val - 1) & 0xFF
            self.write8(self.hl, val)
            self._z = val == 0
            self._n = 1
            return 12
        elif op == 0x36:  # LD (HL), d8
            val = self.fetch8()
            self.write8(self.hl, val)
            return 12
        elif op == 0x37:  # SCF
            self._n = 0
            self._h = 0
            self._c = 1
            return 4
        elif op == 0x38:  # JR C, e
            offset = self.fetch8()
            if self._c:
                if offset & 0x80:
                    offset = -((~offset + 1) & 0xFF)
                self.pc = (self.pc + offset) & 0xFFFF
                return 12
            return 8
        elif op == 0x39:  # ADD HL, SP
            hl = self.hl
            sp = self.sp
            result = hl + sp
            self._n = 0
            self._h = ((hl & 0xFFF) + (sp & 0xFFF)) > 0xFFF
            self._c = result > 0xFFFF
            self.hl = result & 0xFFFF
            return 8
        elif op == 0x3A:  # LD A, (HL-)
            self.a = self.read8(self.hl)
            self.hl = (self.hl - 1) & 0xFFFF
            return 8
        elif op == 0x3B:  # DEC SP
            self.sp = (self.sp - 1) & 0xFFFF
            return 8
        elif op == 0x3C:  # INC A
            self._h = ((self.a & 0x0F) + 1) > 0x0F
            self.a = (self.a + 1) & 0xFF
            self._z = self.a == 0
            self._n = 0
            return 4
        elif op == 0x3D:  # DEC A
            self._h = (self.a & 0x0F) == 0
            self.a = (self.a - 1) & 0xFF
            self._z = self.a == 0
            self._n = 1
            return 4
        elif op == 0x3E:  # LD A, d8
            self.a = self.fetch8()
            return 8
        elif op == 0x3F:  # CCF
            self._n = 0
            self._h = 0
            self._c ^= 1
            return 4
        # Many more instructions omitted – add as needed.
        else:
            # Unimplemented instruction – treat as NOP
            print(f"Unimplemented opcode: 0x{op:02X} at PC={self.pc-1:04X}")
            return 4

    def _exec_cb(self, op):
        # Prefix CB instructions (bit operations, shifts, rotates)
        # Simplified – just enough for common operations.
        reg_map = {0: self.b, 1: self.c, 2: self.d, 3: self.e,
                   4: self.h, 5: self.l, 6: None, 7: self.a}
        if op < 0x40:
            # RLC, RRC, RL, RR, SLA, SRA, SWAP, SRL
            # Not fully implemented; ignore for now.
            return 8
        elif op < 0x80:
            # BIT
            bit = (op >> 3) & 7
            reg = op & 7
            if reg == 6:
                val = self.read8(self.hl)
            else:
                val = reg_map[reg]
            self._z = not (val & (1 << bit))
            self._n = 0
            self._h = 1
            return 8 if reg != 6 else 12
        elif op < 0xC0:
            # RES
            bit = (op >> 3) & 7
            reg = op & 7
            if reg == 6:
                val = self.read8(self.hl)
                val &= ~(1 << bit)
                self.write8(self.hl, val)
            else:
                reg_map[reg] &= ~(1 << bit)
            return 8 if reg != 6 else 16
        else:
            # SET
            bit = (op >> 3) & 7
            reg = op & 7
            if reg == 6:
                val = self.read8(self.hl)
                val |= (1 << bit)
                self.write8(self.hl, val)
            else:
                reg_map[reg] |= (1 << bit)
            return 8 if reg != 6 else 16

# ----------------------------------------------------------------------
# PPU (Picture Processing Unit) – basic rendering
# ----------------------------------------------------------------------
class PPU:
    def __init__(self, mmu):
        self.mmu = mmu
        self.framebuffer = bytearray(SCREEN_W * SCREEN_H * 3)  # RGB
        self.cycles = 0
        self.line = 0
        self.mode = 0  # 0=HBlank, 1=VBlank, 2=OAM, 3=Transfer
        self.ly = 0

    def step(self, cpu_cycles):
        self.cycles += cpu_cycles
        if self.cycles >= 456:  # one scanline
            self.cycles -= 456
            self.ly = (self.ly + 1) % 154
            self.mmu.io[0x44] = self.ly  # LY register

            if self.ly < 144:
                # Rendering mode 3 (transfer) and then mode 0 (HBlank)
                self.mode = 3
                # Simulate mode 3 timing (172 cycles) then mode 0
                # Actually we'll draw scanline here
                self._draw_scanline()
                self.mode = 0
            elif self.ly == 144:
                # VBlank start
                self.mode = 1
                self.mmu.io[0x0F] |= 1  # VBlank interrupt flag
                self._request_interrupt(0)
            else:
                self.mode = 1
            self.mmu.io[0x41] = (self.mmu.io[0x41] & 0xFC) | self.mode

    def _draw_scanline(self):
        lcdc = self.mmu.io[0x40]
        if not (lcdc & 0x80):
            return  # LCD off

        # Background
        if lcdc & 0x01:
            self._draw_background_scanline(lcdc)
        # Sprites
        if lcdc & 0x02:
            self._draw_sprites_scanline(lcdc)

    def _draw_background_scanline(self, lcdc):
        bg_tilemap_base = 0x1C00 if (lcdc & 0x08) else 0x1800
        bg_tiledata_base = 0x0000 if (lcdc & 0x10) else 0x0800  # 8000 or 8800 addressing
        scroll_y = self.mmu.io[0x42]
        scroll_x = self.mmu.io[0x43]
        ly = self.ly

        y = (ly + scroll_y) & 0xFF
        tile_row = y // 8
        y_offset = y % 8

        # For each pixel in scanline
        for x in range(SCREEN_W):
            world_x = (x + scroll_x) & 0xFF
            tile_col = world_x // 8
            x_offset = world_x % 8

            # Get tile index
            map_addr = bg_tilemap_base + tile_row * 32 + tile_col
            tile_idx = self.mmu.vram[map_addr]

            # Get tile data
            if bg_tiledata_base == 0x0000:
                # 8000 method: tile index 0-255
                tile_addr = 0x0000 + tile_idx * 16
            else:
                # 8800 method: signed index
                tile_addr = 0x0800 + ((tile_idx ^ 0x80) - 128) * 16

            # Two bytes per row
            row_addr = tile_addr + y_offset * 2
            low = self.mmu.vram[row_addr]
            high = self.mmu.vram[row_addr + 1]
            bit = 7 - x_offset
            color_id = ((high >> bit) & 1) << 1 | ((low >> bit) & 1)
            # Map to grayscale (for now)
            color = self._get_color(color_id)
            idx = (ly * SCREEN_W + x) * 3
            self.framebuffer[idx:idx+3] = color

    def _draw_sprites_scanline(self, lcdc):
        # Simplified sprite rendering (priority, x-flip ignored)
        sprite_height = 16 if (lcdc & 0x04) else 8
        ly = self.ly
        for i in range(40):
            y = self.mmu.oam[i*4] - 16
            if y <= ly < y + sprite_height:
                x = self.mmu.oam[i*4+1] - 8
                tile_idx = self.mmu.oam[i*4+2]
                attr = self.mmu.oam[i*4+3]
                # Only draw if within screen
                if x < -7 or x >= SCREEN_W:
                    continue
                y_offset = ly - y
                if attr & 0x40:  # Y flip
                    y_offset = sprite_height - 1 - y_offset
                tile_addr = 0x0000 + tile_idx * 16 + y_offset * 2
                low = self.mmu.vram[tile_addr]
                high = self.mmu.vram[tile_addr + 1]
                for px in range(8):
                    screen_x = x + px
                    if screen_x < 0 or screen_x >= SCREEN_W:
                        continue
                    bit = 7 - (px if not (attr & 0x20) else 7-px)
                    color_id = ((high >> bit) & 1) << 1 | ((low >> bit) & 1)
                    if color_id != 0:  # transparent
                        color = self._get_color(color_id)
                        idx = (ly * SCREEN_W + screen_x) * 3
                        self.framebuffer[idx:idx+3] = color

    def _get_color(self, id):
        # BGP register (0xFF47) defines palette for background
        bgp = self.mmu.io[0x47]
        shade = (bgp >> (id * 2)) & 3
        # Simple grayscale: 0=white, 1=light gray, 2=dark gray, 3=black
        gray = [255, 192, 96, 0][shade]
        return bytes([gray, gray, gray])

    def _request_interrupt(self, bit):
        self.mmu.io[0x0F] |= (1 << bit)

    def get_frame(self):
        return bytes(self.framebuffer)

# ----------------------------------------------------------------------
# Joypad handling
# ----------------------------------------------------------------------
class Joypad:
    def __init__(self, mmu):
        self.mmu = mmu
        self.buttons = 0xFF  # 0=pressed

    def press(self, key):
        # Map keys to Game Boy buttons
        mapping = {
            'z': 0,  # A
            'x': 1,  # B
            'Return': 2,  # Select
            'space': 3,  # Start
            'Up': 4,
            'Down': 5,
            'Left': 6,
            'Right': 7,
        }
        if key in mapping:
            bit = mapping[key]
            self.buttons &= ~(1 << bit)
            self._update_joypad_reg()

    def release(self, key):
        mapping = {
            'z': 0,
            'x': 1,
            'Return': 2,
            'space': 3,
            'Up': 4,
            'Down': 5,
            'Left': 6,
            'Right': 7,
        }
        if key in mapping:
            bit = mapping[key]
            self.buttons |= (1 << bit)
            self._update_joypad_reg()

    def _update_joypad_reg(self):
        reg = self.mmu.io[0x00]  # Joypad register
        if not (reg & 0x20):  # Select direction buttons
            lower = self.buttons & 0x0F
        elif not (reg & 0x10):  # Select action buttons
            lower = (self.buttons >> 4) & 0x0F
        else:
            lower = 0x0F
        self.mmu.io[0x00] = (reg & 0xF0) | (lower & 0x0F)

# ----------------------------------------------------------------------
# Emulator Core
# ----------------------------------------------------------------------
class Emulator:
    def __init__(self):
        self.mmu = MMU()
        self.cpu = CPU(self.mmu)
        self.ppu = PPU(self.mmu)
        self.joypad = Joypad(self.mmu)
        self.running = False
        self.rom_loaded = False
        self.frame_ready_callback = None

    def load_rom(self, rom_path):
        with open(rom_path, 'rb') as f:
            data = f.read()
        self.mmu.load_rom(data)
        self.rom_loaded = True
        self.reset()

    def reset(self):
        self.cpu.reset()
        self.ppu = PPU(self.mmu)
        self.joypad = Joypad(self.mmu)

    def run_frame(self):
        """Emulate one frame and return True if frame completed."""
        cycles_this_frame = 0
        while cycles_this_frame < CYCLES_PER_FRAME:
            if self.cpu.halt:
                # HALT: skip until interrupt
                cycles = 4
                cycles_this_frame += cycles
                self.ppu.step(cycles)
                # Check interrupts (simplified)
                if self.mmu.io[0x0F] & self.mmu.ie:
                    self.cpu.halt = False
                continue

            cycles = self.cpu.step()
            cycles_this_frame += cycles
            self.ppu.step(cycles)

            # Handle interrupts (simplified)
            if self.cpu.ime and (self.mmu.io[0x0F] & self.mmu.ie):
                # VBlank is main interrupt we care about
                if (self.mmu.io[0x0F] & 1) and (self.mmu.ie & 1):
                    self.cpu.ime = False
                    self.mmu.io[0x0F] &= ~1
                    self.cpu.push16(self.cpu.pc)
                    self.cpu.pc = 0x0040
                    cycles_this_frame += 20
        return True

    def get_frame(self):
        return self.ppu.get_frame()

# ----------------------------------------------------------------------
# Tkinter GUI
# ----------------------------------------------------------------------
class CatGameboyEmu:
    def __init__(self, root):
        self.root = root
        self.root.title("Cat's Gameboy Emu 1.x")
        self.root.configure(bg='black')
        self.root.resizable(False, False)

        # Emulator instance
        self.emu = Emulator()
        self.emu.frame_ready_callback = self.on_frame_ready

        # GUI elements
        self.create_menu()
        self.create_display()
        self.create_controls()

        # Key bindings
        self.root.bind('<KeyPress>', self.key_press)
        self.root.bind('<KeyRelease>', self.key_release)

        # Emulation thread
        self.running = False
        self.after_id = None
        self.frame_update_interval = 16  # ms (~60 FPS)

    def create_menu(self):
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)

        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Load ROM...", command=self.load_rom)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)

        emu_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Emulation", menu=emu_menu)
        emu_menu.add_command(label="Start", command=self.start_emulation)
        emu_menu.add_command(label="Pause", command=self.pause_emulation)
        emu_menu.add_command(label="Reset", command=self.reset_emulation)

    def create_display(self):
        self.canvas = tk.Canvas(
            self.root,
            width=SCREEN_W * SCALE,
            height=SCREEN_H * SCALE,
            bg='black',
            highlightthickness=0
        )
        self.canvas.pack(padx=10, pady=10)

        # Create a PhotoImage to hold the frame
        self.photo = tk.PhotoImage(width=SCREEN_W, height=SCREEN_H)
        self.canvas_image = self.canvas.create_image(
            0, 0, anchor='nw', image=self.photo
        )
        # Scale the image
        self.canvas.scale(self.canvas_image, 0, 0, SCALE, SCALE)

    def create_controls(self):
        control_frame = tk.Frame(self.root, bg='black')
        control_frame.pack(pady=5)

        # Status label
        self.status_var = tk.StringVar(value="No ROM loaded")
        status_label = tk.Label(
            control_frame,
            textvariable=self.status_var,
            fg='blue',
            bg='black',
            font=('Courier', 10)
        )
        status_label.pack(side='left', padx=10)

        # Buttons
        btn_style = {
            'fg': 'blue',
            'bg': 'black',
            'activeforeground': 'black',
            'activebackground': 'blue',
            'relief': 'flat',
            'borderwidth': 1,
            'font': ('Courier', 9, 'bold')
        }
        tk.Button(control_frame, text="Load ROM", command=self.load_rom, **btn_style).pack(side='left', padx=2)
        tk.Button(control_frame, text="Start", command=self.start_emulation, **btn_style).pack(side='left', padx=2)
        tk.Button(control_frame, text="Pause", command=self.pause_emulation, **btn_style).pack(side='left', padx=2)
        tk.Button(control_frame, text="Reset", command=self.reset_emulation, **btn_style).pack(side='left', padx=2)

    def load_rom(self):
        filepath = filedialog.askopenfilename(
            title="Select Game Boy ROM",
            filetypes=[("Game Boy ROMs", "*.gb *.gbc"), ("All Files", "*.*")]
        )
        if filepath:
            try:
                self.emu.load_rom(filepath)
                self.status_var.set(f"Loaded: {os.path.basename(filepath)}")
                self.reset_emulation()
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load ROM:\n{e}")

    def start_emulation(self):
        if not self.emu.rom_loaded:
            messagebox.showwarning("No ROM", "Please load a ROM first.")
            return
        self.running = True
        self.run_emulation_loop()

    def pause_emulation(self):
        self.running = False
        if self.after_id:
            self.root.after_cancel(self.after_id)
            self.after_id = None
        self.status_var.set("Paused")

    def reset_emulation(self):
        self.emu.reset()
        self.status_var.set("Reset")

    def run_emulation_loop(self):
        if not self.running:
            return
        # Emulate one frame
        self.emu.run_frame()
        # Update display
        self.update_display()
        # Schedule next frame
        self.after_id = self.root.after(self.frame_update_interval, self.run_emulation_loop)

    def update_display(self):
        frame_data = self.emu.get_frame()
        # Convert to PhotoImage format (RGB -> PPM via string)
        ppm_header = f'P6 {SCREEN_W} {SCREEN_H} 255\n'
        ppm_data = ppm_header.encode() + frame_data
        self.photo = tk.PhotoImage(data=ppm_data, format='PPM')
        self.canvas.itemconfig(self.canvas_image, image=self.photo)

    def on_frame_ready(self):
        # Called from emulation thread – we use after_idle to update GUI
        self.root.after_idle(self.update_display)

    def key_press(self, event):
        if not self.running:
            return
        key = event.keysym
        self.emu.joypad.press(key)

    def key_release(self, event):
        if not self.running:
            return
        key = event.keysym
        self.emu.joypad.release(key)

# ----------------------------------------------------------------------
# Main entry point
# ----------------------------------------------------------------------
def main():
    root = tk.Tk()
    app = CatGameboyEmu(root)
    root.mainloop()

if __name__ == "__main__":
    main()