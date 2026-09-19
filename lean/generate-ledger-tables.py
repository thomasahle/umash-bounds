"""Generate untrusted numerical witnesses; every resulting equality uses Lean's kernel.

Run on the Xeon. This script is not part of the trusted proof path.
"""
from pathlib import Path
import json
import re

q = 1 << 64
p = (1 << 61) - 1
source = Path('ProvenHashes/UMASHMaskCensus3125.lean').read_text()
literal = re.search(r'def maskList3125 : List ℕ := (\[[^\n]*\])', source).group(1)
masks = sorted(set(json.loads(literal)))
assert len(masks) == 852

def weight(v):
    patterns = set()
    for j in range(-8, 9):
        z = v + j*p
        if z >= 0 and z % 2 == 0 and (z//2) & v == z//2:
            patterns.add(z//2)
    h, total = 0, 1
    for j in range(64):
        total += 1 << (j-h)
        h += (v >> j) & 1
    return min(q, len(patterns)*total)

weights = [weight(v) for v in masks]

def inverse(s, v):
    x = 0
    for _ in range(64):
        sx = x << 1
        if s != 1:
            sx ^= x << s
        x = v ^ (sx & (q-1))
    return x

def term(x, y):
    a = x[1] ^ y[1]
    if a >= 1 << 63:
        return 0
    e = x[0] ^ a
    h = bin(e).count('1')
    k = min(1 << (1+h-(e >> 63)), 276*(1 << (64-h)),
            16*((1 << ((h+1)//2))+1))
    return k*y[2]

metadata = []
for s in range(1, 16):
    data = [(v, inverse(s,v), w) for v,w in zip(masks,weights)]
    rows = [sum(term(x,y) for y in data) for x in data]
    numerator = sum(rows)
    assert numerator <= 170906186782*q
    prefix = f'''import ProvenHashes.UMASHLedgerTables

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def highLedgerData{s} : List LedgerDatum := [
'''
    prefix += ',\n'.join(f'  ({v}, {a}, {w})' for v,a,w in data) + ']\n\n'
    prefix += f'''/-- Every precomputed inverse and weight is checked against its definition. -/
theorem highLedgerData{s}_correct :
    (sortedUnique maskList3125).map (ledgerDatum {s}) = highLedgerData{s} := by
  apply ledgerData_checked {s} (by decide) highLedgerData{s}
  · decide +kernel
  · decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
'''
    Path(f'Round7HighData{s}.stage.lean').write_text(prefix)
    prepared = [(v ^ a, a, w) for v,a,w in data]
    prep = f'''import ProvenHashes.UMASHHighData{s}
import ProvenHashes.UMASHLedgerFast

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def highLedgerPrepared{s} : List LedgerDatum := [
'''
    prep += ',\n'.join(f'  ({v}, {a}, {w})' for v,a,w in prepared) + ']\n\n'
    prep += f'''theorem highLedgerPrepared{s}_correct :
    highLedgerData{s}.map ledgerPrepare = highLedgerPrepared{s} := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
'''
    Path(f'Round7HighPrepared{s}.stage.lean').write_text(prep)
    metadata.append(dict(s=s, numerator=numerator, rows=rows))
    if s == 1:
        Path('Round7HighTrial.stage.lean').write_text(f'''import ProvenHashes.UMASHHighData1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem highLedger_first_row_certificate :
    ledgerSum (highLedgerData1.take 1) highLedgerData1 = {rows[0]} := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
''')
        Path('Round7HighFastTrial.stage.lean').write_text(f'''import ProvenHashes.UMASHHighPrepared1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem highLedger_fast_first_rows_certificate :
    ledgerFastSum (highLedgerPrepared1.take 32) highLedgerPrepared1 = {sum(rows[:32])} := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
''')

Path('HighLedgerWitnesses.json').write_text(json.dumps(metadata, indent=2)+'\n')
print('Generated 15 tables and exact row witnesses; these still require Lean checking.')
