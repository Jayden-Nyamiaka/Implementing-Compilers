"""
show_asm.py:
  Make assembly language instructions in S-expressions easier to identify.
"""

import sys, re

def convert_instr(line):
    line = re.sub('Addq',  'addq',  line)
    line = re.sub('Subq',  'subq',  line)
    line = re.sub('Negq',  'negq',  line)
    line = re.sub('Movq',  'movq',  line)
    line = re.sub('Pushq', 'pushq', line)
    line = re.sub('Popq',  'popq',  line)
    line = re.sub('Callq', 'callq', line)
    line = re.sub('Retq',  'retq',  line)
    line = re.sub('Jmp',   'jmp',   line)
    return line

def convert_imm(line):
    line = re.sub(r'\(Imm ([-]?\d+)\)', r'$\1', line)
    return line

def transform_deref_reg(m):
    reg = '%' + m.group(1).lower()
    offset = m.group(2)
    return f'{offset}({reg})'

def convert_deref_reg(line):
    line = re.sub(r'\(Deref (.{3}) ([-]?\d+)\)', transform_deref_reg, line)
    return line

def transform_reg(m):
    return '%' + m.group(1).lower()

def convert_reg(line):
    line = re.sub(r'\(Reg (.{3})\)', transform_reg, line)
    return line

def convert_line(line):
    line = convert_instr(line)
    line = convert_imm(line)
    line = convert_deref_reg(line)
    line = convert_reg(line)
    return line

for line in sys.stdin:
    print(convert_line(line), end='')

