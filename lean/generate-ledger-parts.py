"""Partition exact ledgers into independent kernel-checked row blocks."""
from pathlib import Path
import json
import re
import sys

size = int(sys.argv[1]) if len(sys.argv) > 1 else 32
metadata = json.loads(Path('HighLedgerWitnesses.json').read_text())
jobs = []
for record in metadata:
    s, rows = record['s'], record['rows']
    source = Path(f'Round7HighPrepared{s}.stage.lean').read_text()
    data = re.search(r'def highLedgerPrepared\d+ : List LedgerDatum := \[(.*?)\]\n',
                     source, re.S).group(1).strip().split(',\n')
    assert len(data) == 852
    count = (len(data)+size-1)//size
    parts = f'''import ProvenHashes.UMASHHighPrepared{s}
import ProvenHashes.UMASHLedgerPacked

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

'''
    for j in range(count):
        parts += f'def highLedgerPart{s}_{j} : List LedgerDatum := [\n'
        parts += ',\n'.join(data[j*size:(j+1)*size]) + ']\n\n'
    concatenation = ' ++ '.join(f'highLedgerPart{s}_{j}' for j in range(count))
    parts += f'''theorem highLedgerPrepared{s}_partition :
    highLedgerPrepared{s} = {concatenation} := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
'''
    Path(f'Round7HighParts{s}.stage.lean').write_text(parts)
    for j in range(count):
        value = sum(rows[j*size:(j+1)*size])
        stage = f'Round7HighPart{s}_{j}.stage.lean'
        module = f'ProvenHashes.UMASHHighPart{s}_{j}'
        direct_import = ''
        direct_rewrite = ''
        Path(stage).write_text(f'''import ProvenHashes.UMASHHighParts{s}{direct_import}

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows {j*size} through {min((j+1)*size,852)-1}. -/
theorem highLedgerPart{s}_{j}_certificate :
    ledgerPackedSum highLedgerPart{s}_{j} highLedgerPrepared{s} = {value} := by
{direct_rewrite}  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
''')
        jobs.append(dict(s=s, j=j, stage=stage, module=module))
    assembled = '\n'.join(f'import ProvenHashes.UMASHHighPart{s}_{j}' for j in range(count))
    assembled += f'''

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] highLedgerPrepared{s}

/-- The full high ledger is the exact sum of the checked row blocks. -/
theorem phenh_high_numerator_{s} :
    phenhHighLedgerNumerator {s} = {record['numerator']} := by
  rw [phenhHighLedger_eq_table, highLedgerData{s}_correct,
    ledgerSum_eq_fast, highLedgerPrepared{s}_correct, ledgerFastSum_eq_packed]
  conv_lhs => arg 1; rw [highLedgerPrepared{s}_partition]
  simp only [ledgerPackedSum_append, '''
    assembled += ', '.join(f'highLedgerPart{s}_{j}_certificate' for j in range(count)) + ']\n'
    assembled += '-- CHECKPOINT\n\nend ProvenHashes.UMASH\n'
    Path(f'Round7HighCertificate{s}.stage.lean').write_text(assembled)

Path('HighLedgerJobs.json').write_text(json.dumps(jobs, indent=2)+'\n')
print(f'Generated {len(jobs)} exact row-block certificates, {size} rows per block.')
