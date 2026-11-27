"""Check the project lemmas and axioms in the export rooted at the two targets."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
config = json.loads((root / "comparator.json").read_text())
required = {
    "Vu.Revised." + name for name in (
        "graph_structure", "uniform_of_structure", "extracting_dense_pieces",
        "energy_regular_refinement", "witness_energy", "Classes.regular_cut",
        "Classes.coefficient_cut", "Classes.common_witness", "Classes.tests_and_omissions",
        "pack_neighbor_groups", "rooted_component_count", "omit_columns", "two_moments",
        "sum_lower_tail", "union_lower_tail_of_bound", "coloring_round", "finish_state",
    )
}
historical = {"Vu.graph_decomposition", "Vu.Revised.graph_decomposition", "Vu.coloring_round",
              "Vu.regular_refinement_vertices", "Vu.pack_neighbor_groups"}
names = {0: ""}
theorems = set()
axioms = set()
digest = hashlib.sha256()
with tempfile.TemporaryFile() as export:
    subprocess.run(["lake", "env", "leanexport", config["solution_module"], "--",
                    *config["theorem_names"]], cwd=root, stdout=export, check=True)
    export.seek(0)
    for line in export:
        digest.update(line)
        if line.startswith(b'{"in":'):
            record = json.loads(line)
            item = record.get("str") or record["num"]
            prefix = names[item["pre"]]
            suffix = str(item.get("str", item.get("i")))
            names[record["in"]] = prefix + "." + suffix if prefix else suffix
        elif line.startswith(b'{"thm":'):
            theorems.add(names[json.loads(line)["thm"]["name"]])
        elif line.startswith(b'{"axiom":'):
            axioms.add(names[json.loads(line)["axiom"]["name"]])
missing = required - theorems
unwanted = historical & theorems
if missing or unwanted or axioms != set(config["permitted_axioms"]):
    raise ValueError(f"Missing {sorted(missing)}, historical {sorted(unwanted)}, axioms {sorted(axioms)}")
report = {
    "roots": config["theorem_names"], "export_sha256": digest.hexdigest(),
    "axioms": sorted(axioms), "number_of_project_theorems": sum(s.startswith("Vu.") for s in theorems),
    "required_revised_lemmas_present": sorted(required),
    "historical_alternative_lemmas_absent": sorted(historical),
}
(root/"evidence"/"proof-route.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
