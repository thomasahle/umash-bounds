"""Independently checkpoint the 59 remaining finite class-count lemmas."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import subprocess


def check(r):
    name = 'UMASHClassCard' + str(r)
    log = Path('logs') / ('stage-' + name + '.txt')
    with log.open('w') as f:
        result = subprocess.run(['python3', 'stage-part2.py', 'staged/' + name + '.lean',
                                 'ProvenHashes.' + name, '0'], stdout=f, stderr=subprocess.STDOUT)
    return r, result.returncode, str(log)


failed = []
with ThreadPoolExecutor(max_workers=4) as pool:
    # Check the extremal case first, then every remaining integer separately.
    futures = [pool.submit(check, r) for r in [63] + list(range(5, 63))]
    for future in as_completed(futures):
        r, code, log = future.result()
        print(('PASS' if code == 0 else 'FAIL'), r, log, flush=True)
        if code:
            failed.append(r)
if failed:
    raise SystemExit('Failed class counts: ' + repr(failed))
print('All 59 additional class counts passed.', flush=True)
