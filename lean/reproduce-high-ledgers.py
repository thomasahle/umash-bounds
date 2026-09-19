"""Rebuild the large kernel certificates with bounded process concurrency.

Run through reproduce-part2.sh --recheck-high-ledgers. The Mathlib cache must
already be present. This script never deletes a cache or regenerates witnesses.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import resource
import subprocess
import sys

workers = int(sys.argv[1]) if len(sys.argv) > 1 else 4
assert 1 <= workers <= 7
resource.setrlimit(resource.RLIMIT_AS, (24 * 1024**3, 24 * 1024**3))
logs = Path('logs/reproduce-high-ledgers')
logs.mkdir(parents=True, exist_ok=True)

def build(module):
    log = logs / (module.rsplit('.', 1)[-1] + '.txt')
    with log.open('w') as output:
        subprocess.run(['nice', '-n', '10', 'taskset', '-c', '56-63',
                        'lake', 'build', module], stdout=output,
                       stderr=subprocess.STDOUT, check=True)
    print('CHECKED ' + module, flush=True)

for module in ['UMASHLedgerTables', 'UMASHLedgerFast', 'UMASHLedgerPacked']:
    build('ProvenHashes.' + module)
for kind in ['Data', 'Prepared', 'Parts']:
    with ThreadPoolExecutor(max_workers=workers) as executor:
        list(executor.map(build, (f'ProvenHashes.UMASHHigh{kind}{s}' for s in range(1, 16))))
jobs = json.loads(Path('HighLedgerJobs.json').read_text())
with ThreadPoolExecutor(max_workers=workers) as executor:
    list(executor.map(build, (job['module'] for job in jobs)))
with ThreadPoolExecutor(max_workers=workers) as executor:
    list(executor.map(build, (f'ProvenHashes.UMASHHighCertificate{s}' for s in range(1, 16))))
build('ProvenHashes.UMASHPHENHSharp')
