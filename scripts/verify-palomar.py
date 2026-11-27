"""Run the project's pinned Comparator with both independent kernels used by Palomar."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
os.chdir(root)
config = json.loads(Path('comparator.json').read_text())
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
config['external_kernels'] = {
    'nanoda': [str(prefix / 'bin/nanoda_bin')],
    'con-ron': [str(prefix / 'bin/con-ron')],
}
with tempfile.TemporaryDirectory() as tmp:
    config_file = Path(tmp) / 'comparator-local.json'
    config_file.write_text(json.dumps(config))
    subprocess.run(['lake', 'comparator', '--config', str(config_file)], check=True)
