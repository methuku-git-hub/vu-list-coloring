"""Independently check the exported proofs listed in the Lean axiom audit."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]

def run(command, **kwargs):
    return subprocess.run(command, cwd=root, check=True, **kwargs)

audit = run(["lake", "env", "lean", "Audit.lean"], capture_output=True, text=True).stdout
names = re.findall(r"^(Vu\.[\w.]+): \[", audit, re.MULTILINE)
if not names or "Vu.main_result" not in names or len(names) != len(set(names)):
    raise ValueError("Expected a nonempty list of distinct proved declarations from Audit.lean")
prefix = Path(run(["lean", "--print-prefix"], capture_output=True, text=True).stdout.strip())
allowed = json.loads((root / "comparator.json").read_text())["permitted_axioms"]
with tempfile.TemporaryDirectory() as tmp:
    path = Path(tmp) / "export.ndjson"
    with path.open("wb") as f:
        run(["lake", "env", "leanexport", "Vu", "Solution", "--", *names], stdout=f)
    config = Path(tmp) / "nanoda.json"
    config.write_text(json.dumps({
        "export_file_path": str(path), "permitted_axioms": allowed,
        "unpermitted_axiom_hard_error": True, "num_threads": 4,
        "nat_extension": True, "string_extension": True,
    }))
    run([prefix / "bin/nanoda_bin", config])
    ron = run([prefix / "bin/con-ron", "--verified", "--jobs=3", path], capture_output=True, text=True)
    with path.open("rb") as f:
        digest = hashlib.file_digest(f, "sha256").hexdigest()
    report = {
        "scope": "Unconditional Solution, audited auxiliary proofs, and their transitive dependencies",
        "declarations": names, "permitted_axioms": allowed,
        "toolchain": (root / "lean-toolchain").read_text().strip(),
        "export_sha256": digest, "export_bytes": path.stat().st_size,
        "nanoda_exit_code": 0, "con_ron_exit_code": 0,
        "con_ron_output": (ron.stdout + ron.stderr).strip().splitlines(),
    }
    (root / "evidence/kernel-replay.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Both kernels accepted the export of {len(names)} audited declarations.")
