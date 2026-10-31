#!/usr/bin/env python3
"""Check that every ```lean block of README.md occurs word for word in Ex89/Model.lean or Ex89/Main.lean."""
import re, sys
readme = open('README.md').read()
src = open('Ex89/Model.lean').read()
try:
    src += open('Ex89/Main.lean').read()
except FileNotFoundError:
    pass
blocks = re.findall(r'```lean\n(.*?)```', readme, re.S)
bad = [b for b in blocks if b.strip() not in src]
for b in bad:
    print('NOT IN LEAN FILES:\n' + b)
print(f'{len(blocks)} blocks, {len(bad)} differ')
sys.exit(1 if bad or not blocks else 0)
