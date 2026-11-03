#!/usr/bin/env python3
"""Check that every ```lean block of README.md occurs word for word in Ex89/Model.lean or one of the Ex89/Main*.lean files."""
import re, sys
readme = open('README.md').read()
src = open('Ex89/Model.lean').read()
src += open('Ex89/Main.lean').read()
src += open('Ex89/Main40.lean').read()
src += open('Ex89/Main48.lean').read()
src += open('Ex89/Main28.lean').read()
src += open('Ex89/Main33.lean').read()
src += open('Ex89/Main60.lean').read()
src += open('Ex89/Main65.lean').read()
src += open('Ex89/Main36.lean').read()
src += open('Ex89/Main39.lean').read()
blocks = re.findall(r'```lean\n(.*?)```', readme, re.S)
bad = [b for b in blocks if b.strip() not in src]
for b in bad:
    print('NOT IN LEAN FILES:\n' + b)
print(f'{len(blocks)} blocks, {len(bad)} differ')
sys.exit(1 if bad or not blocks else 0)
