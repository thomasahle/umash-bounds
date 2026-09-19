"""Check independent ledger blocks, recording one lake build for each theorem."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import subprocess
import sys
import threading

workers = int(sys.argv[1]) if len(sys.argv) > 1 else 4
jobs = json.loads(Path('HighLedgerJobs.json').read_text())
failed = threading.Event()

def build(stage_module):
    if failed.is_set():
        raise RuntimeError('A prior certificate failed; stopping this batch.')
    stage, module = stage_module
    result = subprocess.run(['python3', 'build-round6-stage.py', stage, module],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        failed.set()
        print(result.stdout[-12000:], flush=True)
        raise RuntimeError(f'Failed: {module}')
    print('CHECKED '+module, flush=True)

for batch in [
    [(f'Round7HighParts{s}.stage.lean', f'ProvenHashes.UMASHHighParts{s}') for s in range(1,16)],
    [(job['stage'], job['module']) for job in jobs],
    [(f'Round7HighCertificate{s}.stage.lean', f'ProvenHashes.UMASHHighCertificate{s}') for s in range(1,16)]
]:
    with ThreadPoolExecutor(max_workers=workers) as executor:
        list(executor.map(build, batch))
