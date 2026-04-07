#!/usr/bin/env python3
"""
Cat's Gameboy Emu 4k v2.0
A single-file Game Boy (DMG) emulator targeting commercial ROM compatibility.
Full LR35902 CPU · MBC1/2/3/5 · Timer · All interrupts · Window · Sprites
(C) 1999-2026 A.C Holdings / Team Flames
GUI: tkinter | Requires: Python 3.10+
"""

import tkinter as tk
from tkinter import filedialog, messagebox
import time
import sys
import os
from array import array

# --------------------------------------------------------------------------
# Constants
# --------------------------------------------------------------------------
SCREEN_W = 160
SCREEN_H = 144
SCALE = 3
CYCLES_PER_FRAME = 70224  # ~59.7275 Hz NTSC

# DMG boot-state register values (post-bootrom)
BOOT_A = 0x01; BOOT_F = 0xB0
BOOT_B = 0x00; BOOT_C = 0x13
BOOT_D = 0x00; BOOT_E = 0xD8
BOOT_H = 0x01; BOOT_L = 0x4D
BOOT_SP = 0xFFFE; BOOT_PC = 0x0100

# --------------------------------------------------------------------------
# MBC (Memory Bank Controller) implementations
# --------------------------------------------------------------------------
class MBC0:
    """No mapper — 32KB ROM, optional 8KB RAM."""
    def __init__(self, rom, ram_size):
        self.rom = rom
        self.ram = bytearray(ram_size) if ram_size else bytearray(0x2000)
        self.ram_enable = False

    def read_rom(self, addr):
        if addr < len(self.rom):
            return self.rom[addr]
        return 0xFF

    def read_ram(self, addr):
        offset = addr - 0xA000
        if self.ram_enable and offset < len(self.ram):
            return self.ram[offset]
        return 0xFF

    def write_rom(self, addr, val):
        pass  # ROM area writes ignored for MBC0

    def write_ram(self, addr, val):
        offset = addr - 0xA000
        if self.ram_enable and offset < len(self.ram):
            self.ram[offset] = val


class MBC1:
    """MBC1 — up to 2MB ROM / 32KB RAM."""
    def __init__(self, rom, ram_size):
        self.rom = rom
        self.ram = bytearray(ram_size) if ram_size else bytearray(0x8000)
        self.ram_enable = False
        self.rom_bank = 1
        self.ram_bank = 0
        self.mode = 0  # 0=ROM banking, 1=RAM banking
        self.rom_bank_count = max(2, len(rom) // 0x4000)

    def read_rom(self, addr):
        if addr < 0x4000:
            if self.mode == 1:
                bank = (self.ram_bank << 5) % self.rom_bank_count
            else:
                bank = 0
            offset = bank * 0x4000 + addr
        else:
            bank = ((self.ram_bank << 5) | self.rom_bank) % self.rom_bank_count
            offset = bank * 0x4000 + (addr - 0x4000)
        if offset < len(self.rom):
            return self.rom[offset]
        return 0xFF

    def read_ram(self, addr):
        if not self.ram_enable or not self.ram:
            return 0xFF
        bank = self.ram_bank if self.mode == 1 else 0
        offset = bank * 0x2000 + (addr - 0xA000)
        if offset < len(self.ram):
            return self.ram[offset]
        return 0xFF

    def write_rom(self, addr, val):
        if addr < 0x2000:
            self.ram_enable = (val & 0x0F) == 0x0A
        elif addr < 0x4000:
            bank = val & 0x1F
            if bank == 0:
                bank = 1
            self.rom_bank = bank
        elif addr < 0x6000:
            self.ram_bank = val & 0x03
        else:
            self.mode = val & 1

    def write_ram(self, addr, val):
        if not self.ram_enable or not self.ram:
            return
        bank = self.ram_bank if self.mode == 1 else 0
        offset = bank * 0x2000 + (addr - 0xA000)
        if offset < len(self.ram):
            self.ram[offset] = val


class MBC2:
    """MBC2 — up to 256KB ROM, built-in 512×4bit RAM."""
    def __init__(self, rom, ram_size):
        self.rom = rom
        self.ram = bytearray(512)
        self.ram_enable = False
        self.rom_bank = 1
        self.rom_bank_count = max(2, len(rom) // 0x4000)

    def read_rom(self, addr):
        if addr < 0x4000:
            return self.rom[addr] if addr < len(self.rom) else 0xFF
        bank = self.rom_bank % self.rom_bank_count
        offset = bank * 0x4000 + (addr - 0x4000)
        return self.rom[offset] if offset < len(self.rom) else 0xFF

    def read_ram(self, addr):
        if self.ram_enable:
            return self.ram[(addr - 0xA000) & 0x1FF] & 0x0F
        return 0xFF

    def write_rom(self, addr, val):
        if addr < 0x4000:
            if addr & 0x0100:
                bank = val & 0x0F
                if bank == 0:
                    bank = 1
                self.rom_bank = bank
            else:
                self.ram_enable = (val & 0x0F) == 0x0A

    def write_ram(self, addr, val):
        if self.ram_enable:
            self.ram[(addr - 0xA000) & 0x1FF] = val & 0x0F


class MBC3:
    """MBC3 — up to 2MB ROM / 32KB RAM + RTC."""
    def __init__(self, rom, ram_size):
        self.rom = rom
        self.ram = bytearray(ram_size) if ram_size else bytearray(0x8000)
        self.ram_enable = False
        self.rom_bank = 1
        self.ram_bank = 0
        self.rom_bank_count = max(2, len(rom) // 0x4000)
        # RTC registers (simplified)
        self.rtc = [0] * 5  # S, M, H, DL, DH
        self.rtc_latch = 0
        self.rtc_mapped = False

    def read_rom(self, addr):
        if addr < 0x4000:
            return self.rom[addr] if addr < len(self.rom) else 0xFF
        bank = self.rom_bank % self.rom_bank_count
        offset = bank * 0x4000 + (addr - 0x4000)
        return self.rom[offset] if offset < len(self.rom) else 0xFF

    def read_ram(self, addr):
        if not self.ram_enable:
            return 0xFF
        if self.ram_bank <= 3:
            offset = self.ram_bank * 0x2000 + (addr - 0xA000)
            if offset < len(self.ram):
                return self.ram[offset]
            return 0xFF
        elif 0x08 <= self.ram_bank <= 0x0C:
            return self.rtc[self.ram_bank - 0x08]
        return 0xFF

    def write_rom(self, addr, val):
        if addr < 0x2000:
            self.ram_enable = (val & 0x0F) == 0x0A
        elif addr < 0x4000:
            bank = val & 0x7F
            if bank == 0:
                bank = 1
            self.rom_bank = bank
        elif addr < 0x6000:
            self.ram_bank = val
        else:
            # RTC latch
            if self.rtc_latch == 0 and val == 1:
                t = time.localtime()
                self.rtc[0] = t.tm_sec
                self.rtc[1] = t.tm_min
                self.rtc[2] = t.tm_hour
                day = t.tm_yday & 0xFF
                self.rtc[3] = day & 0xFF
                self.rtc[4] = (day >> 8) & 1
            self.rtc_latch = val

    def write_ram(self, addr, val):
        if not self.ram_enable:
            return
        if self.ram_bank <= 3:
            offset = self.ram_bank * 0x2000 + (addr - 0xA000)
            if offset < len(self.ram):
                self.ram[offset] = val
        elif 0x08 <= self.ram_bank <= 0x0C:
            self.rtc[self.ram_bank - 0x08] = val


class MBC5:
    """MBC5 — up to 8MB ROM / 128KB RAM."""
    def __init__(self, rom, ram_size):
        self.rom = rom
        self.ram = bytearray(ram_size) if ram_size else bytearray(0x20000)
        self.ram_enable = False
        self.rom_bank = 1
        self.ram_bank = 0
        self.rom_bank_count = max(2, len(rom) // 0x4000)

    def read_rom(self, addr):
        if addr < 0x4000:
            return self.rom[addr] if addr < len(self.rom) else 0xFF
        bank = self.rom_bank % self.rom_bank_count
        offset = bank * 0x4000 + (addr - 0x4000)
        return self.rom[offset] if offset < len(self.rom) else 0xFF

    def read_ram(self, addr):
        if not self.ram_enable:
            return 0xFF
        offset = self.ram_bank * 0x2000 + (addr - 0xA000)
        if offset < len(self.ram):
            return self.ram[offset]
        return 0xFF

    def write_rom(self, addr, val):
        if addr < 0x2000:
            self.ram_enable = (val & 0x0F) == 0x0A
        elif addr < 0x3000:
            self.rom_bank = (self.rom_bank & 0x100) | val
        elif addr < 0x4000:
            self.rom_bank = (self.rom_bank & 0xFF) | ((val & 1) << 8)
        elif addr < 0x6000:
            self.ram_bank = val & 0x0F

    def write_ram(self, addr, val):
        if not self.ram_enable:
            return
        offset = self.ram_bank * 0x2000 + (addr - 0xA000)
        if offset < len(self.ram):
            self.ram[offset] = val


# --------------------------------------------------------------------------
# RAM size LUT from cart header byte 0x0149
# --------------------------------------------------------------------------
RAM_SIZES = {0: 0, 1: 0x800, 2: 0x2000, 3: 0x8000, 4: 0x20000, 5: 0x10000}

def make_mbc(rom):
    """Create the appropriate MBC for the given ROM data."""
    cart_type = rom[0x147] if len(rom) > 0x147 else 0
    ram_code = rom[0x149] if len(rom) > 0x149 else 0
    ram_size = RAM_SIZES.get(ram_code, 0x2000)
    # Map cart type byte -> MBC class
    if cart_type in (0x00, 0x08, 0x09):
        return MBC0(rom, ram_size)
    elif cart_type in (0x01, 0x02, 0x03):
        return MBC1(rom, ram_size)
    elif cart_type in (0x05, 0x06):
        return MBC2(rom, ram_size)
    elif cart_type in (0x0F, 0x10, 0x11, 0x12, 0x13):
        return MBC3(rom, ram_size)
    elif cart_type in (0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E):
        return MBC5(rom, ram_size)
    else:
        # Fallback: try MBC1 for unknowns (covers many edge cases)
        print(f"[warn] Unknown cart type 0x{cart_type:02X}, defaulting to MBC1")
        return MBC1(rom, ram_size)


# --------------------------------------------------------------------------
# MMU (Memory Management Unit)
# --------------------------------------------------------------------------
class MMU:
    def __init__(self):
        self.mbc = None
        self.vram = bytearray(0x2000)
        self.wram = bytearray(0x2000)
        self.oam = bytearray(0xA0)
        self.io = bytearray(0x80)
        self.hram = bytearray(0x7F)
        self.ie = 0
        # Post-boot I/O state
        self._init_io()

    def _init_io(self):
        self.io[0x00] = 0xCF  # P1/JOYP
        self.io[0x01] = 0x00  # SB
        self.io[0x02] = 0x7E  # SC
        self.io[0x04] = 0xAB  # DIV
        self.io[0x05] = 0x00  # TIMA
        self.io[0x06] = 0x00  # TMA
        self.io[0x07] = 0xF8  # TAC
        self.io[0x0F] = 0xE1  # IF
        self.io[0x10] = 0x80  # NR10
        self.io[0x11] = 0xBF  # NR11
        self.io[0x12] = 0xF3  # NR12
        self.io[0x14] = 0xBF  # NR14
        self.io[0x16] = 0x3F  # NR21
        self.io[0x17] = 0x00  # NR22
        self.io[0x19] = 0xBF  # NR24
        self.io[0x1A] = 0x7F  # NR30
        self.io[0x1B] = 0xFF  # NR31
        self.io[0x1C] = 0x9F  # NR32
        self.io[0x1E] = 0xBF  # NR33
        self.io[0x20] = 0xFF  # NR41
        self.io[0x21] = 0x00  # NR42
        self.io[0x22] = 0x00  # NR43
        self.io[0x23] = 0xBF  # NR44
        self.io[0x24] = 0x77  # NR50
        self.io[0x25] = 0xF3  # NR51
        self.io[0x26] = 0xF1  # NR52
        self.io[0x40] = 0x91  # LCDC
        self.io[0x41] = 0x85  # STAT
        self.io[0x42] = 0x00  # SCY
        self.io[0x43] = 0x00  # SCX
        self.io[0x44] = 0x00  # LY
        self.io[0x45] = 0x00  # LYC
        self.io[0x47] = 0xFC  # BGP
        self.io[0x48] = 0xFF  # OBP0
        self.io[0x49] = 0xFF  # OBP1
        self.io[0x4A] = 0x00  # WY
        self.io[0x4B] = 0x00  # WX

    def load_rom(self, rom_data):
        self.mbc = make_mbc(bytearray(rom_data))

    def read(self, addr):
        if addr < 0x8000:
            return self.mbc.read_rom(addr)
        elif addr < 0xA000:
            return self.vram[addr - 0x8000]
        elif addr < 0xC000:
            return self.mbc.read_ram(addr)
        elif addr < 0xE000:
            return self.wram[addr - 0xC000]
        elif addr < 0xFE00:
            return self.wram[addr - 0xE000]  # Echo
        elif addr < 0xFEA0:
            return self.oam[addr - 0xFE00]
        elif addr < 0xFF00:
            return 0xFF  # Unusable
        elif addr < 0xFF80:
            return self.io[addr - 0xFF00]
        elif addr < 0xFFFF:
            return self.hram[addr - 0xFF80]
        else:
            return self.ie

    def write(self, addr, val):
        val &= 0xFF
        if addr < 0x8000:
            self.mbc.write_rom(addr, val)
        elif addr < 0xA000:
            self.vram[addr - 0x8000] = val
        elif addr < 0xC000:
            self.mbc.write_ram(addr, val)
        elif addr < 0xE000:
            self.wram[addr - 0xC000] = val
        elif addr < 0xFE00:
            self.wram[addr - 0xE000] = val
        elif addr < 0xFEA0:
            self.oam[addr - 0xFE00] = val
        elif addr < 0xFF00:
            pass  # Unusable
        elif addr < 0xFF80:
            self._write_io(addr - 0xFF00, val)
        elif addr < 0xFFFF:
            self.hram[addr - 0xFF80] = val
        else:
            self.ie = val

    def _write_io(self, offset, val):
        if offset == 0x00:  # P1/JOYP — only bits 4-5 writable
            self.io[0] = (val & 0x30) | (self.io[0] & 0xCF)
        elif offset == 0x04:  # DIV — any write resets to 0
            self.io[0x04] = 0
        elif offset == 0x41:  # STAT — bits 0-2 read-only
            self.io[0x41] = (val & 0x78) | (self.io[0x41] & 0x07)
        elif offset == 0x44:  # LY — read-only (write resets)
            self.io[0x44] = 0
        elif offset == 0x46:  # DMA
            src = (val << 8) & 0xFFFF
            for i in range(0xA0):
                self.oam[i] = self.read(src + i)
        else:
            self.io[offset] = val


# --------------------------------------------------------------------------
# Timer
# --------------------------------------------------------------------------
class Timer:
    """DIV (FF04), TIMA (FF05), TMA (FF06), TAC (FF07)."""
    CLOCKS = [1024, 16, 64, 256]  # CPU clocks per TIMA tick

    def __init__(self, mmu):
        self.mmu = mmu
        self.div_counter = 0
        self.tima_counter = 0

    def step(self, cycles):
        io = self.mmu.io
        # DIV increments at 16384 Hz = every 256 CPU clocks
        self.div_counter += cycles
        while self.div_counter >= 256:
            self.div_counter -= 256
            io[0x04] = (io[0x04] + 1) & 0xFF

        # TIMA
        tac = io[0x07]
        if tac & 0x04:  # Timer enabled
            freq = self.CLOCKS[tac & 0x03]
            self.tima_counter += cycles
            while self.tima_counter >= freq:
                self.tima_counter -= freq
                tima = io[0x05] + 1
                if tima > 0xFF:
                    tima = io[0x06]  # reload from TMA
                    io[0x0F] |= 0x04  # Timer interrupt flag
                io[0x05] = tima & 0xFF


# --------------------------------------------------------------------------
# CPU — Full LR35902
# --------------------------------------------------------------------------
class CPU:
    def __init__(self, mmu):
        self.mmu = mmu
        self.reset()

    def reset(self):
        self.a = BOOT_A; self.f = BOOT_F
        self.b = BOOT_B; self.c = BOOT_C
        self.d = BOOT_D; self.e = BOOT_E
        self.h = BOOT_H; self.l = BOOT_L
        self.sp = BOOT_SP; self.pc = BOOT_PC
        self.ime = True
        self.ime_pending = False
        self.halted = False
        self.stopped = False

    # -- Flag accessors --
    @property
    def fz(self): return (self.f >> 7) & 1
    @fz.setter
    def fz(self, v): self.f = (self.f & 0x7F) | ((v & 1) << 7)

    @property
    def fn(self): return (self.f >> 6) & 1
    @fn.setter
    def fn(self, v): self.f = (self.f & 0xBF) | ((v & 1) << 6)

    @property
    def fh(self): return (self.f >> 5) & 1
    @fh.setter
    def fh(self, v): self.f = (self.f & 0xDF) | ((v & 1) << 5)

    @property
    def fc(self): return (self.f >> 4) & 1
    @fc.setter
    def fc(self, v): self.f = (self.f & 0xEF) | ((v & 1) << 4)

    # -- 16-bit register pairs --
    def get_af(self): return (self.a << 8) | (self.f & 0xF0)
    def set_af(self, v): self.a = (v >> 8) & 0xFF; self.f = v & 0xF0
    def get_bc(self): return (self.b << 8) | self.c
    def set_bc(self, v): self.b = (v >> 8) & 0xFF; self.c = v & 0xFF
    def get_de(self): return (self.d << 8) | self.e
    def set_de(self, v): self.d = (v >> 8) & 0xFF; self.e = v & 0xFF
    def get_hl(self): return (self.h << 8) | self.l
    def set_hl(self, v): self.h = (v >> 8) & 0xFF; self.l = v & 0xFF

    # -- Memory helpers --
    def rb(self, a): return self.mmu.read(a)
    def wb(self, a, v): self.mmu.write(a, v & 0xFF)
    def rw(self, a): return self.rb(a) | (self.rb(a + 1) << 8)
    def ww(self, a, v): self.wb(a, v & 0xFF); self.wb(a + 1, (v >> 8) & 0xFF)

    def fetch(self):
        v = self.rb(self.pc)
        self.pc = (self.pc + 1) & 0xFFFF
        return v

    def fetch16(self):
        lo = self.fetch()
        hi = self.fetch()
        return (hi << 8) | lo

    def push(self, v):
        self.sp = (self.sp - 1) & 0xFFFF
        self.wb(self.sp, (v >> 8) & 0xFF)
        self.sp = (self.sp - 1) & 0xFFFF
        self.wb(self.sp, v & 0xFF)

    def pop(self):
        lo = self.rb(self.sp); self.sp = (self.sp + 1) & 0xFFFF
        hi = self.rb(self.sp); self.sp = (self.sp + 1) & 0xFFFF
        return (hi << 8) | lo

    # -- Register getters/setters by index (for opcode decoding) --
    def _get_r(self, idx):
        """Get register value by 3-bit index: B=0 C=1 D=2 E=3 H=4 L=5 (HL)=6 A=7"""
        if idx == 0: return self.b
        elif idx == 1: return self.c
        elif idx == 2: return self.d
        elif idx == 3: return self.e
        elif idx == 4: return self.h
        elif idx == 5: return self.l
        elif idx == 6: return self.rb(self.get_hl())
        else: return self.a

    def _set_r(self, idx, v):
        v &= 0xFF
        if idx == 0: self.b = v
        elif idx == 1: self.c = v
        elif idx == 2: self.d = v
        elif idx == 3: self.e = v
        elif idx == 4: self.h = v
        elif idx == 5: self.l = v
        elif idx == 6: self.wb(self.get_hl(), v)
        else: self.a = v

    # -- ALU helpers --
    def _add(self, v):
        r = self.a + v
        self.fh = ((self.a & 0xF) + (v & 0xF)) > 0xF
        self.fc = r > 0xFF
        self.a = r & 0xFF
        self.fz = self.a == 0
        self.fn = 0

    def _adc(self, v):
        c = self.fc
        r = self.a + v + c
        self.fh = ((self.a & 0xF) + (v & 0xF) + c) > 0xF
        self.fc = r > 0xFF
        self.a = r & 0xFF
        self.fz = self.a == 0
        self.fn = 0

    def _sub(self, v):
        r = self.a - v
        self.fh = (self.a & 0xF) < (v & 0xF)
        self.fc = r < 0
        self.a = r & 0xFF
        self.fz = self.a == 0
        self.fn = 1

    def _sbc(self, v):
        c = self.fc
        r = self.a - v - c
        self.fh = (self.a & 0xF) < (v & 0xF) + c
        self.fc = r < 0
        self.a = r & 0xFF
        self.fz = self.a == 0
        self.fn = 1

    def _and(self, v):
        self.a &= v
        self.fz = self.a == 0
        self.fn = 0; self.fh = 1; self.fc = 0

    def _xor(self, v):
        self.a ^= v
        self.fz = self.a == 0
        self.fn = 0; self.fh = 0; self.fc = 0

    def _or(self, v):
        self.a |= v
        self.fz = self.a == 0
        self.fn = 0; self.fh = 0; self.fc = 0

    def _cp(self, v):
        r = self.a - v
        self.fz = (r & 0xFF) == 0
        self.fn = 1
        self.fh = (self.a & 0xF) < (v & 0xF)
        self.fc = r < 0

    def _inc(self, v):
        r = (v + 1) & 0xFF
        self.fz = r == 0
        self.fn = 0
        self.fh = ((v & 0xF) + 1) > 0xF
        return r

    def _dec(self, v):
        r = (v - 1) & 0xFF
        self.fz = r == 0
        self.fn = 1
        self.fh = (v & 0xF) == 0
        return r

    def _add_hl(self, v):
        hl = self.get_hl()
        r = hl + v
        self.fn = 0
        self.fh = ((hl & 0xFFF) + (v & 0xFFF)) > 0xFFF
        self.fc = r > 0xFFFF
        self.set_hl(r & 0xFFFF)

    # -- Interrupt handling --
    def handle_interrupts(self):
        iflag = self.mmu.io[0x0F]
        ie = self.mmu.ie
        pending = iflag & ie & 0x1F
        if pending:
            self.halted = False
            if self.ime:
                self.ime = False
                for bit in range(5):
                    if pending & (1 << bit):
                        self.mmu.io[0x0F] &= ~(1 << bit)
                        self.push(self.pc)
                        self.pc = 0x0040 + bit * 8
                        return 20
        return 0

    # -- Main step --
    def step(self):
        if self.halted:
            return 4

        if self.ime_pending:
            self.ime = True
            self.ime_pending = False

        op = self.fetch()
        if op == 0xCB:
            return self._exec_cb(self.fetch())
        return self._exec(op)

    def _exec(self, op):
        # ----- 0x00-0x3F: Misc / LD 16bit / INC DEC 8bit / LD 8bit imm / Rotates / JR -----
        if op == 0x00: return 4  # NOP
        elif op == 0x01: self.set_bc(self.fetch16()); return 12
        elif op == 0x02: self.wb(self.get_bc(), self.a); return 8
        elif op == 0x03: self.set_bc((self.get_bc() + 1) & 0xFFFF); return 8
        elif op == 0x04: self.b = self._inc(self.b); return 4
        elif op == 0x05: self.b = self._dec(self.b); return 4
        elif op == 0x06: self.b = self.fetch(); return 8
        elif op == 0x07:  # RLCA
            c = (self.a >> 7) & 1
            self.a = ((self.a << 1) | c) & 0xFF
            self.f = c << 4  # Z=0 N=0 H=0 C=bit7
            return 4
        elif op == 0x08:  # LD (a16), SP
            self.ww(self.fetch16(), self.sp); return 20
        elif op == 0x09: self._add_hl(self.get_bc()); return 8
        elif op == 0x0A: self.a = self.rb(self.get_bc()); return 8
        elif op == 0x0B: self.set_bc((self.get_bc() - 1) & 0xFFFF); return 8
        elif op == 0x0C: self.c = self._inc(self.c); return 4
        elif op == 0x0D: self.c = self._dec(self.c); return 4
        elif op == 0x0E: self.c = self.fetch(); return 8
        elif op == 0x0F:  # RRCA
            c = self.a & 1
            self.a = ((self.a >> 1) | (c << 7)) & 0xFF
            self.f = c << 4
            return 4
        elif op == 0x10:  # STOP
            self.fetch()  # consume next byte
            self.stopped = True
            return 4
        elif op == 0x11: self.set_de(self.fetch16()); return 12
        elif op == 0x12: self.wb(self.get_de(), self.a); return 8
        elif op == 0x13: self.set_de((self.get_de() + 1) & 0xFFFF); return 8
        elif op == 0x14: self.d = self._inc(self.d); return 4
        elif op == 0x15: self.d = self._dec(self.d); return 4
        elif op == 0x16: self.d = self.fetch(); return 8
        elif op == 0x17:  # RLA
            c = self.fc
            self.fc = (self.a >> 7) & 1
            self.a = ((self.a << 1) | c) & 0xFF
            self.fz = 0; self.fn = 0; self.fh = 0
            return 4
        elif op == 0x18:  # JR e
            e = self.fetch()
            if e & 0x80: e -= 256
            self.pc = (self.pc + e) & 0xFFFF
            return 12
        elif op == 0x19: self._add_hl(self.get_de()); return 8
        elif op == 0x1A: self.a = self.rb(self.get_de()); return 8
        elif op == 0x1B: self.set_de((self.get_de() - 1) & 0xFFFF); return 8
        elif op == 0x1C: self.e = self._inc(self.e); return 4
        elif op == 0x1D: self.e = self._dec(self.e); return 4
        elif op == 0x1E: self.e = self.fetch(); return 8
        elif op == 0x1F:  # RRA
            c = self.fc
            self.fc = self.a & 1
            self.a = ((self.a >> 1) | (c << 7)) & 0xFF
            self.fz = 0; self.fn = 0; self.fh = 0
            return 4
        elif op == 0x20:  # JR NZ
            e = self.fetch()
            if not self.fz:
                if e & 0x80: e -= 256
                self.pc = (self.pc + e) & 0xFFFF; return 12
            return 8
        elif op == 0x21: self.set_hl(self.fetch16()); return 12
        elif op == 0x22: self.wb(self.get_hl(), self.a); self.set_hl((self.get_hl() + 1) & 0xFFFF); return 8
        elif op == 0x23: self.set_hl((self.get_hl() + 1) & 0xFFFF); return 8
        elif op == 0x24: self.h = self._inc(self.h); return 4
        elif op == 0x25: self.h = self._dec(self.h); return 4
        elif op == 0x26: self.h = self.fetch(); return 8
        elif op == 0x27:  # DAA
            a = self.a
            if self.fn:
                if self.fc: a -= 0x60
                if self.fh: a -= 0x06
            else:
                if self.fc or a > 0x99: a += 0x60; self.fc = 1
                if self.fh or (a & 0x0F) > 0x09: a += 0x06
            self.a = a & 0xFF
            self.fz = self.a == 0
            self.fh = 0
            return 4
        elif op == 0x28:  # JR Z
            e = self.fetch()
            if self.fz:
                if e & 0x80: e -= 256
                self.pc = (self.pc + e) & 0xFFFF; return 12
            return 8
        elif op == 0x29: self._add_hl(self.get_hl()); return 8
        elif op == 0x2A: self.a = self.rb(self.get_hl()); self.set_hl((self.get_hl() + 1) & 0xFFFF); return 8
        elif op == 0x2B: self.set_hl((self.get_hl() - 1) & 0xFFFF); return 8
        elif op == 0x2C: self.l = self._inc(self.l); return 4
        elif op == 0x2D: self.l = self._dec(self.l); return 4
        elif op == 0x2E: self.l = self.fetch(); return 8
        elif op == 0x2F:  # CPL
            self.a ^= 0xFF; self.fn = 1; self.fh = 1; return 4
        elif op == 0x30:  # JR NC
            e = self.fetch()
            if not self.fc:
                if e & 0x80: e -= 256
                self.pc = (self.pc + e) & 0xFFFF; return 12
            return 8
        elif op == 0x31: self.sp = self.fetch16(); return 12
        elif op == 0x32: self.wb(self.get_hl(), self.a); self.set_hl((self.get_hl() - 1) & 0xFFFF); return 8
        elif op == 0x33: self.sp = (self.sp + 1) & 0xFFFF; return 8
        elif op == 0x34:  # INC (HL)
            v = self._inc(self.rb(self.get_hl()))
            self.wb(self.get_hl(), v); return 12
        elif op == 0x35:  # DEC (HL)
            v = self._dec(self.rb(self.get_hl()))
            self.wb(self.get_hl(), v); return 12
        elif op == 0x36: self.wb(self.get_hl(), self.fetch()); return 12
        elif op == 0x37: self.fn = 0; self.fh = 0; self.fc = 1; return 4  # SCF
        elif op == 0x38:  # JR C
            e = self.fetch()
            if self.fc:
                if e & 0x80: e -= 256
                self.pc = (self.pc + e) & 0xFFFF; return 12
            return 8
        elif op == 0x39: self._add_hl(self.sp); return 8
        elif op == 0x3A: self.a = self.rb(self.get_hl()); self.set_hl((self.get_hl() - 1) & 0xFFFF); return 8
        elif op == 0x3B: self.sp = (self.sp - 1) & 0xFFFF; return 8
        elif op == 0x3C: self.a = self._inc(self.a); return 4
        elif op == 0x3D: self.a = self._dec(self.a); return 4
        elif op == 0x3E: self.a = self.fetch(); return 8
        elif op == 0x3F: self.fn = 0; self.fh = 0; self.fc ^= 1; return 4  # CCF

        # ----- 0x40-0x7F: LD r, r' block + HALT (0x76) -----
        elif 0x40 <= op <= 0x7F:
            if op == 0x76:  # HALT
                self.halted = True
                return 4
            dst = (op >> 3) & 7
            src = op & 7
            self._set_r(dst, self._get_r(src))
            return 8 if (src == 6 or dst == 6) else 4

        # ----- 0x80-0xBF: ALU A, r -----
        elif 0x80 <= op <= 0xBF:
            r = op & 7
            v = self._get_r(r)
            alu = (op >> 3) & 7
            if alu == 0: self._add(v)
            elif alu == 1: self._adc(v)
            elif alu == 2: self._sub(v)
            elif alu == 3: self._sbc(v)
            elif alu == 4: self._and(v)
            elif alu == 5: self._xor(v)
            elif alu == 6: self._or(v)
            elif alu == 7: self._cp(v)
            return 8 if r == 6 else 4

        # ----- 0xC0-0xFF: Control flow, stack, 16-bit, immediate ALU, misc -----
        elif op == 0xC0:  # RET NZ
            if not self.fz: self.pc = self.pop(); return 20
            return 8
        elif op == 0xC1: self.set_bc(self.pop()); return 12
        elif op == 0xC2:  # JP NZ
            a = self.fetch16()
            if not self.fz: self.pc = a; return 16
            return 12
        elif op == 0xC3: self.pc = self.fetch16(); return 16  # JP a16
        elif op == 0xC4:  # CALL NZ
            a = self.fetch16()
            if not self.fz: self.push(self.pc); self.pc = a; return 24
            return 12
        elif op == 0xC5: self.push(self.get_bc()); return 16
        elif op == 0xC6: self._add(self.fetch()); return 8
        elif op == 0xC7: self.push(self.pc); self.pc = 0x00; return 16  # RST 00
        elif op == 0xC8:  # RET Z
            if self.fz: self.pc = self.pop(); return 20
            return 8
        elif op == 0xC9: self.pc = self.pop(); return 16  # RET
        elif op == 0xCA:  # JP Z
            a = self.fetch16()
            if self.fz: self.pc = a; return 16
            return 12
        # 0xCB handled above
        elif op == 0xCC:  # CALL Z
            a = self.fetch16()
            if self.fz: self.push(self.pc); self.pc = a; return 24
            return 12
        elif op == 0xCD:  # CALL a16
            a = self.fetch16(); self.push(self.pc); self.pc = a; return 24
        elif op == 0xCE: self._adc(self.fetch()); return 8
        elif op == 0xCF: self.push(self.pc); self.pc = 0x08; return 16  # RST 08
        elif op == 0xD0:  # RET NC
            if not self.fc: self.pc = self.pop(); return 20
            return 8
        elif op == 0xD1: self.set_de(self.pop()); return 12
        elif op == 0xD2:  # JP NC
            a = self.fetch16()
            if not self.fc: self.pc = a; return 16
            return 12
        elif op == 0xD4:  # CALL NC
            a = self.fetch16()
            if not self.fc: self.push(self.pc); self.pc = a; return 24
            return 12
        elif op == 0xD5: self.push(self.get_de()); return 16
        elif op == 0xD6: self._sub(self.fetch()); return 8
        elif op == 0xD7: self.push(self.pc); self.pc = 0x10; return 16  # RST 10
        elif op == 0xD8:  # RET C
            if self.fc: self.pc = self.pop(); return 20
            return 8
        elif op == 0xD9:  # RETI
            self.pc = self.pop(); self.ime = True; return 16
        elif op == 0xDA:  # JP C
            a = self.fetch16()
            if self.fc: self.pc = a; return 16
            return 12
        elif op == 0xDC:  # CALL C
            a = self.fetch16()
            if self.fc: self.push(self.pc); self.pc = a; return 24
            return 12
        elif op == 0xDE: self._sbc(self.fetch()); return 8
        elif op == 0xDF: self.push(self.pc); self.pc = 0x18; return 16  # RST 18
        elif op == 0xE0:  # LDH (a8), A
            self.wb(0xFF00 + self.fetch(), self.a); return 12
        elif op == 0xE1: self.set_hl(self.pop()); return 12
        elif op == 0xE2:  # LD (C), A
            self.wb(0xFF00 + self.c, self.a); return 8
        elif op == 0xE5: self.push(self.get_hl()); return 16
        elif op == 0xE6: self._and(self.fetch()); return 8
        elif op == 0xE7: self.push(self.pc); self.pc = 0x20; return 16  # RST 20
        elif op == 0xE8:  # ADD SP, e8
            e = self.fetch()
            if e & 0x80: e -= 256
            r = self.sp + e
            self.fz = 0; self.fn = 0
            self.fh = ((self.sp & 0xF) + (e & 0xF)) & 0x10 != 0
            self.fc = ((self.sp & 0xFF) + (e & 0xFF)) & 0x100 != 0
            self.sp = r & 0xFFFF
            return 16
        elif op == 0xE9: self.pc = self.get_hl(); return 4  # JP HL
        elif op == 0xEA:  # LD (a16), A
            self.wb(self.fetch16(), self.a); return 16
        elif op == 0xEE: self._xor(self.fetch()); return 8
        elif op == 0xEF: self.push(self.pc); self.pc = 0x28; return 16  # RST 28
        elif op == 0xF0:  # LDH A, (a8)
            self.a = self.rb(0xFF00 + self.fetch()); return 12
        elif op == 0xF1: self.set_af(self.pop()); return 12
        elif op == 0xF2:  # LD A, (C)
            self.a = self.rb(0xFF00 + self.c); return 8
        elif op == 0xF3: self.ime = False; return 4  # DI
        elif op == 0xF5: self.push(self.get_af()); return 16
        elif op == 0xF6: self._or(self.fetch()); return 8
        elif op == 0xF7: self.push(self.pc); self.pc = 0x30; return 16  # RST 30
        elif op == 0xF8:  # LD HL, SP+e8
            e = self.fetch()
            if e & 0x80: e -= 256
            r = self.sp + e
            self.fz = 0; self.fn = 0
            self.fh = ((self.sp & 0xF) + (e & 0xF)) & 0x10 != 0
            self.fc = ((self.sp & 0xFF) + (e & 0xFF)) & 0x100 != 0
            self.set_hl(r & 0xFFFF)
            return 12
        elif op == 0xF9: self.sp = self.get_hl(); return 8  # LD SP, HL
        elif op == 0xFA:  # LD A, (a16)
            self.a = self.rb(self.fetch16()); return 16
        elif op == 0xFB:  # EI (delayed by one instruction)
            self.ime_pending = True; return 4
        elif op == 0xFE: self._cp(self.fetch()); return 8
        elif op == 0xFF: self.push(self.pc); self.pc = 0x38; return 16  # RST 38
        else:
            # Undefined opcodes (0xD3, 0xDB, 0xDD, 0xE3, 0xE4, 0xEB, 0xEC, 0xED, 0xF4, 0xFC, 0xFD)
            return 4  # Treat as NOP

    # ---- CB prefix: full implementation ----
    def _exec_cb(self, op):
        r = op & 7
        v = self._get_r(r)
        cyc = 16 if r == 6 else 8
        group = op >> 3

        if group == 0:  # RLC
            c = (v >> 7) & 1
            v = ((v << 1) | c) & 0xFF
            self.fc = c; self.fz = v == 0; self.fn = 0; self.fh = 0
        elif group == 1:  # RRC
            c = v & 1
            v = ((v >> 1) | (c << 7)) & 0xFF
            self.fc = c; self.fz = v == 0; self.fn = 0; self.fh = 0
        elif group == 2:  # RL
            c = self.fc
            self.fc = (v >> 7) & 1
            v = ((v << 1) | c) & 0xFF
            self.fz = v == 0; self.fn = 0; self.fh = 0
        elif group == 3:  # RR
            c = self.fc
            self.fc = v & 1
            v = ((v >> 1) | (c << 7)) & 0xFF
            self.fz = v == 0; self.fn = 0; self.fh = 0
        elif group == 4:  # SLA
            self.fc = (v >> 7) & 1
            v = (v << 1) & 0xFF
            self.fz = v == 0; self.fn = 0; self.fh = 0
        elif group == 5:  # SRA
            self.fc = v & 1
            v = ((v >> 1) | (v & 0x80)) & 0xFF
            self.fz = v == 0; self.fn = 0; self.fh = 0
        elif group == 6:  # SWAP
            v = ((v >> 4) | (v << 4)) & 0xFF
            self.fz = v == 0; self.fn = 0; self.fh = 0; self.fc = 0
        elif group == 7:  # SRL
            self.fc = v & 1
            v = (v >> 1) & 0xFF
            self.fz = v == 0; self.fn = 0; self.fh = 0
        elif 8 <= group < 16:  # BIT
            bit = (op >> 3) & 7
            self.fz = not (v & (1 << bit))
            self.fn = 0; self.fh = 1
            return 12 if r == 6 else 8  # BIT doesn't write back
        elif 16 <= group < 24:  # RES
            bit = (op >> 3) & 7
            v &= ~(1 << bit)
        else:  # SET (24-31)
            bit = (op >> 3) & 7
            v |= (1 << bit)

        self._set_r(r, v)
        return cyc


# --------------------------------------------------------------------------
# PPU — with window layer, proper palettes, sprite priority
# --------------------------------------------------------------------------
class PPU:
    # DMG palette: 4 shades of green-ish gray (classic GB LCD feel)
    COLORS = [
        (224, 248, 208),  # 0: lightest
        (136, 192, 112),  # 1: light
        (52, 104, 86),    # 2: dark
        (8, 24, 32),      # 3: darkest
    ]

    def __init__(self, mmu):
        self.mmu = mmu
        self.framebuffer = bytearray(SCREEN_W * SCREEN_H * 3)
        self.bg_priority = bytearray(SCREEN_W * SCREEN_H)  # per-pixel BG color index
        self.cycles = 0
        self.window_line_counter = 0
        self.frame_ready = False

    def step(self, cpu_cycles):
        io = self.mmu.io
        lcdc = io[0x40]
        if not (lcdc & 0x80):  # LCD off
            return

        self.cycles += cpu_cycles

        ly = io[0x44]
        stat = io[0x41]

        while self.cycles >= 456:
            self.cycles -= 456
            ly = (ly + 1) % 154
            io[0x44] = ly

            if ly < 144:
                self._draw_scanline(ly)
            elif ly == 144:
                io[0x0F] |= 0x01  # VBlank IF
                if stat & 0x10:   # Mode 1 STAT interrupt
                    io[0x0F] |= 0x02
                self.frame_ready = True
                self.window_line_counter = 0

            # LYC=LY compare
            if ly == io[0x45]:
                stat |= 0x04  # Coincidence flag
                if stat & 0x40:  # LYC=LY STAT interrupt
                    io[0x0F] |= 0x02
            else:
                stat &= ~0x04

            # Update mode bits (simplified)
            if ly >= 144:
                mode = 1
            else:
                mode = 0  # We draw instantly so we're always in HBlank from the CPU's POV
            stat = (stat & 0xFC) | mode
            io[0x41] = stat

    def _draw_scanline(self, ly):
        lcdc = self.mmu.io[0x40]
        # Clear scanline priority buffer
        row_start = ly * SCREEN_W
        for x in range(SCREEN_W):
            self.bg_priority[row_start + x] = 0

        # Background
        if lcdc & 0x01:
            self._draw_bg(ly, lcdc)
        else:
            # Fill white when BG is off
            idx = ly * SCREEN_W * 3
            for x in range(SCREEN_W):
                r, g, b = self.COLORS[0]
                self.framebuffer[idx] = r; self.framebuffer[idx+1] = g; self.framebuffer[idx+2] = b
                idx += 3

        # Window
        if (lcdc & 0x21) == 0x21:  # Window enabled + BG enabled
            self._draw_window(ly, lcdc)

        # Sprites
        if lcdc & 0x02:
            self._draw_sprites(ly, lcdc)

    def _get_palette(self, pal_reg):
        """Decode a palette register into 4 RGB tuples."""
        p = self.mmu.io[pal_reg]
        return [self.COLORS[(p >> (i * 2)) & 3] for i in range(4)]

    def _draw_bg(self, ly, lcdc):
        tilemap = 0x1C00 if (lcdc & 0x08) else 0x1800
        signed_mode = not (lcdc & 0x10)
        scy = self.mmu.io[0x42]
        scx = self.mmu.io[0x43]
        pal = self._get_palette(0x47)
        vram = self.mmu.vram
        y = (ly + scy) & 0xFF
        tile_row = (y >> 3) & 31
        y_off = y & 7
        idx = ly * SCREEN_W * 3
        row_start = ly * SCREEN_W

        for x in range(SCREEN_W):
            wx = (x + scx) & 0xFF
            tile_col = (wx >> 3) & 31
            x_off = wx & 7

            map_addr = tilemap + tile_row * 32 + tile_col
            ti = vram[map_addr]
            if signed_mode:
                if ti > 127: ti -= 256
                tile_addr = 0x1000 + ti * 16
            else:
                tile_addr = ti * 16

            ra = tile_addr + y_off * 2
            lo = vram[ra]
            hi = vram[ra + 1]
            bit = 7 - x_off
            cid = ((hi >> bit) & 1) << 1 | ((lo >> bit) & 1)
            self.bg_priority[row_start + x] = cid
            r, g, b = pal[cid]
            self.framebuffer[idx] = r; self.framebuffer[idx+1] = g; self.framebuffer[idx+2] = b
            idx += 3

    def _draw_window(self, ly, lcdc):
        wy = self.mmu.io[0x4A]
        wx = self.mmu.io[0x4B] - 7
        if ly < wy:
            return

        tilemap = 0x1C00 if (lcdc & 0x40) else 0x1800
        signed_mode = not (lcdc & 0x10)
        pal = self._get_palette(0x47)
        vram = self.mmu.vram
        win_y = self.window_line_counter
        tile_row = (win_y >> 3) & 31
        y_off = win_y & 7
        drawn = False
        row_start = ly * SCREEN_W

        for x in range(SCREEN_W):
            sx = x - wx
            if sx < 0:
                continue
            drawn = True
            tile_col = (sx >> 3) & 31
            x_off = sx & 7

            map_addr = tilemap + tile_row * 32 + tile_col
            ti = vram[map_addr]
            if signed_mode:
                if ti > 127: ti -= 256
                tile_addr = 0x1000 + ti * 16
            else:
                tile_addr = ti * 16

            ra = tile_addr + y_off * 2
            lo = vram[ra]
            hi = vram[ra + 1]
            bit = 7 - x_off
            cid = ((hi >> bit) & 1) << 1 | ((lo >> bit) & 1)
            self.bg_priority[row_start + x] = cid
            r, g, b = pal[cid]
            idx = (ly * SCREEN_W + x) * 3
            self.framebuffer[idx] = r; self.framebuffer[idx+1] = g; self.framebuffer[idx+2] = b

        if drawn:
            self.window_line_counter += 1

    def _draw_sprites(self, ly, lcdc):
        sprite_h = 16 if (lcdc & 0x04) else 8
        oam = self.mmu.oam
        vram = self.mmu.vram
        pal0 = self._get_palette(0x48)
        pal1 = self._get_palette(0x49)
        row_start = ly * SCREEN_W

        # Collect sprites on this line (max 10 per line, sorted by X for priority)
        sprites = []
        for i in range(40):
            base = i * 4
            sy = oam[base] - 16
            if sy <= ly < sy + sprite_h:
                sx = oam[base + 1] - 8
                sprites.append((sx, i))
        # DMG priority: lower X first, then lower OAM index
        sprites.sort(key=lambda s: (s[0], s[1]))
        sprites = sprites[:10]
        # Draw in reverse order so higher-priority sprites overwrite
        for sx, i in reversed(sprites):
            base = i * 4
            sy = oam[base] - 16
            tile = oam[base + 2]
            attr = oam[base + 3]
            pal = pal1 if (attr & 0x10) else pal0
            bg_over = attr & 0x80
            y_flip = attr & 0x40
            x_flip = attr & 0x20

            if sprite_h == 16:
                tile &= 0xFE  # Ignore bit 0 for 8x16

            y_off = ly - sy
            if y_flip:
                y_off = sprite_h - 1 - y_off

            ta = tile * 16 + y_off * 2
            if ta + 1 >= len(vram):
                continue
            lo = vram[ta]
            hi = vram[ta + 1]

            for px in range(8):
                screen_x = sx + px
                if screen_x < 0 or screen_x >= SCREEN_W:
                    continue
                bit = 7 - (px if not x_flip else 7 - px)
                cid = ((hi >> bit) & 1) << 1 | ((lo >> bit) & 1)
                if cid == 0:  # Transparent
                    continue
                # BG-over-OBJ: sprite hidden behind BG colors 1-3
                if bg_over and self.bg_priority[row_start + screen_x] != 0:
                    continue
                r, g, b = pal[cid]
                idx = (ly * SCREEN_W + screen_x) * 3
                self.framebuffer[idx] = r; self.framebuffer[idx+1] = g; self.framebuffer[idx+2] = b

    def get_frame(self):
        return bytes(self.framebuffer)


# --------------------------------------------------------------------------
# Joypad
# --------------------------------------------------------------------------
class Joypad:
    """
    Buttons stored as bits: 0=pressed, 1=released (active low like real HW).
    Low nibble = D-pad (Right Left Up Down), High nibble = Buttons (Start Select B A).
    """
    def __init__(self, mmu):
        self.mmu = mmu
        self.rows = [0x0F, 0x0F]  # [0]=directions, [1]=buttons (all released)

    def press(self, key):
        mapping = {
            'Right': (0, 0), 'Left': (0, 1), 'Up': (0, 2), 'Down': (0, 3),
            'z': (1, 0), 'x': (1, 1), 'Return': (1, 2), 'space': (1, 3),
        }
        if key in mapping:
            row, bit = mapping[key]
            self.rows[row] &= ~(1 << bit)
            self.mmu.io[0x0F] |= 0x10  # Joypad interrupt
            self.update()

    def release(self, key):
        mapping = {
            'Right': (0, 0), 'Left': (0, 1), 'Up': (0, 2), 'Down': (0, 3),
            'z': (1, 0), 'x': (1, 1), 'Return': (1, 2), 'space': (1, 3),
        }
        if key in mapping:
            row, bit = mapping[key]
            self.rows[row] |= (1 << bit)
            self.update()

    def update(self):
        reg = self.mmu.io[0x00]
        result = 0x0F
        if not (reg & 0x10):  # Select buttons
            result &= self.rows[1]
        if not (reg & 0x20):  # Select d-pad
            result &= self.rows[0]
        self.mmu.io[0x00] = (reg & 0xF0) | result


# --------------------------------------------------------------------------
# Emulator Core
# --------------------------------------------------------------------------
class Emulator:
    def __init__(self):
        self.mmu = MMU()
        self.cpu = CPU(self.mmu)
        self.ppu = PPU(self.mmu)
        self.timer = Timer(self.mmu)
        self.joypad = Joypad(self.mmu)
        self.rom_loaded = False

    def load_rom(self, path):
        with open(path, 'rb') as f:
            data = f.read()
        self.mmu.load_rom(data)
        self.rom_loaded = True
        self.reset()

    def reset(self):
        self.cpu.reset()
        self.ppu = PPU(self.mmu)
        self.timer = Timer(self.mmu)
        self.joypad = Joypad(self.mmu)
        self.mmu._init_io()

    def run_frame(self):
        cycles = 0
        while cycles < CYCLES_PER_FRAME:
            ic = self.cpu.handle_interrupts()
            if ic:
                cycles += ic
                self.ppu.step(ic)
                self.timer.step(ic)
                continue
            c = self.cpu.step()
            cycles += c
            self.ppu.step(c)
            self.timer.step(c)
            self.joypad.update()
        return self.ppu.get_frame()


# --------------------------------------------------------------------------
# tkinter GUI
# --------------------------------------------------------------------------
class CatGameboyEmu:
    def __init__(self, root):
        self.root = root
        self.root.title("Cat's Gameboy Emu 4k v2.0 — A.C Holdings")
        self.root.configure(bg='#081820')
        self.root.resizable(False, False)

        self.emu = Emulator()
        self.running = False
        self.after_id = None

        self._build_menu()
        self._build_display()
        self._build_status()

        self.root.bind('<KeyPress>', self._key_down)
        self.root.bind('<KeyRelease>', self._key_up)

    def _build_menu(self):
        mb = tk.Menu(self.root)
        self.root.config(menu=mb)
        fm = tk.Menu(mb, tearoff=0)
        mb.add_cascade(label="File", menu=fm)
        fm.add_command(label="Open ROM…", command=self._open_rom)
        fm.add_separator()
        fm.add_command(label="Exit", command=self.root.quit)
        em = tk.Menu(mb, tearoff=0)
        mb.add_cascade(label="Emulation", menu=em)
        em.add_command(label="Run", command=self._start)
        em.add_command(label="Pause", command=self._pause)
        em.add_command(label="Reset", command=self._reset)

    def _build_display(self):
        w = SCREEN_W * SCALE
        h = SCREEN_H * SCALE
        self.canvas = tk.Canvas(self.root, width=w, height=h, bg='#081820', highlightthickness=0)
        self.canvas.pack(padx=8, pady=8)
        # PPM header for raw frame → PhotoImage conversion
        self._ppm_hdr = f'P6 {SCREEN_W} {SCREEN_H} 255\n'.encode()
        # Create initial scaled photo and canvas image
        self.photo = tk.PhotoImage(width=w, height=h)
        self.canvas_img = self.canvas.create_image(0, 0, anchor='nw', image=self.photo)

    def _build_status(self):
        f = tk.Frame(self.root, bg='#081820')
        f.pack(pady=4)
        self.status = tk.StringVar(value="No ROM loaded")
        tk.Label(f, textvariable=self.status, fg='#88C070', bg='#081820',
                 font=('Courier', 10)).pack(side='left', padx=8)
        sty = dict(fg='#88C070', bg='#344860', activeforeground='#E0F8D0',
                   activebackground='#34685E', relief='flat', bd=1,
                   font=('Courier', 9, 'bold'))
        tk.Button(f, text="Open ROM", command=self._open_rom, **sty).pack(side='left', padx=2)
        tk.Button(f, text="Run", command=self._start, **sty).pack(side='left', padx=2)
        tk.Button(f, text="Pause", command=self._pause, **sty).pack(side='left', padx=2)
        tk.Button(f, text="Reset", command=self._reset, **sty).pack(side='left', padx=2)
        # Controls help
        help_text = "Z=A  X=B  Enter=Select  Space=Start  Arrows=D-Pad"
        tk.Label(self.root, text=help_text, fg='#34685E', bg='#081820',
                 font=('Courier', 8)).pack(pady=(0, 4))

    def _open_rom(self):
        path = filedialog.askopenfilename(
            title="Select Game Boy ROM",
            filetypes=[("GB ROMs", "*.gb *.gbc"), ("All", "*.*")])
        if path:
            try:
                self._pause()
                self.emu.load_rom(path)
                self.status.set(f"Loaded: {os.path.basename(path)}")
            except Exception as e:
                messagebox.showerror("Error", str(e))

    def _start(self):
        if not self.emu.rom_loaded:
            messagebox.showwarning("No ROM", "Load a ROM first.")
            return
        if self.running:
            return  # already running, don't stack loops
        self.running = True
        self.status.set("Running")
        self.root.focus_set()  # ensure keyboard focus
        self._loop()

    def _pause(self):
        self.running = False
        if self.after_id:
            self.root.after_cancel(self.after_id)
            self.after_id = None
        self.root.title("Cat's Gameboy Emu 4k v2.0 — A.C Holdings")
        self.status.set("Paused")

    def _reset(self):
        self._pause()
        self.emu.reset()
        # Clear display to black
        self.photo = tk.PhotoImage(width=SCREEN_W * SCALE, height=SCREEN_H * SCALE)
        self.canvas.itemconfig(self.canvas_img, image=self.photo)
        self.status.set("Reset")

    def _loop(self):
        if not self.running:
            return
        t0 = time.perf_counter()
        try:
            frame = self.emu.run_frame()
        except Exception as e:
            self._pause()
            self.status.set(f"CPU error: {e}")
            return
        # Build native-res PhotoImage from raw RGB PPM, then zoom up
        # Must keep ref to raw — tkinter zoomed images reference the original internally
        self._raw_photo = tk.PhotoImage(data=self._ppm_hdr + frame, format='PPM')
        self.photo = self._raw_photo.zoom(SCALE, SCALE)
        self.canvas.itemconfig(self.canvas_img, image=self.photo)
        # FPS in title
        elapsed_ms = (time.perf_counter() - t0) * 1000
        fps = 1000.0 / max(elapsed_ms, 0.1)
        self.root.title(f"Cat's Gameboy Emu 4k v2.0 — {fps:.0f} FPS")
        delay = max(1, int(16.67 - elapsed_ms))
        self.after_id = self.root.after(delay, self._loop)

    def _key_down(self, e):
        self.emu.joypad.press(e.keysym)

    def _key_up(self, e):
        self.emu.joypad.release(e.keysym)


# --------------------------------------------------------------------------
# Entry
# --------------------------------------------------------------------------
def main():
    root = tk.Tk()
    app = CatGameboyEmu(root)
    root.mainloop()

if __name__ == "__main__":
    main()
