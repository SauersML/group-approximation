"""Check proposals against fixed statements and Lean's kernel on remote CPUs.

At most two single-thread Lean processes, each with a 20-second wall limit.
Model output cannot replace the theorem statement or add declarations.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import time

from bh_gpu_pilot import LEAN_IMPORTS, PROBES


def false_control_witness():
    identity = (0, 1, 2)
    a = (1, 0, 2)
    x = (1, 2, 0)

    def mul(p, q):
        return tuple(p[q[i]] for i in range(3))

    y = mul(x, x)
    h = {identity, a}
    k = {identity, x, y}
    assert h & k == {identity}
    assert all(mul(p, q) in h for p, q in itertools.product(h, repeat=2))
    assert all(mul(p, q) in k for p, q in itertools.product(k, repeat=2))
    assert x != y and mul(mul(a, x), a) == y
    return {"group": "S3", "composition": "p*q = p after q", "H": sorted(h),
            "K": sorted(k), "x": x, "y": y, "a": a, "b": a}


def tactic_body(text):
    blocks = re.findall(r"```(?:lean4?|Lean4?)?\s*\n(.*?)```", text, re.S)
    if not blocks:
        raise ValueError("No fenced tactic body")
    body = blocks[-1].strip()
    if body.startswith("by\n"):
        body = body[3:]
    forbidden = r"\b(sorry\w*|admit|axiom|native_decide|ofReduceBool|run_tac|run_elab|elab|unsafe|IO|Lean|import|namespace|theorem|lemma|def|instance|set_option|macro|syntax|attribute|notation|inductive|opaque)\b|#"
    if re.search(forbidden, body):
        raise ValueError("Forbidden declaration, escape or untrusted proof primitive")
    return body


def preflight_rows():
    """Authored calibration, explicitly separate from neural proposals."""
    finish = """
have hK : y * x⁻¹ ∈ K := K.mul_mem hy (K.inv_mem hx)
have hi : y * x⁻¹ ∈ H ⊓ K := ⟨hH, hK⟩
rw [hdis] at hi
have hone : y * x⁻¹ = 1 := hi
exact (mul_inv_eq_one.mp hone).symm
"""
    normalizer = """have hH : y * x⁻¹ ∈ H := by
  rw [heq]
  simpa only [mul_assoc] using H.mul_mem ha (hnorm x hx b hb)
""" + finish
    commuting = """have hbx : x * b * x⁻¹ = b := by
  rw [← hcomm b hb x hx, mul_assoc, mul_inv_cancel, mul_one]
have hH : y * x⁻¹ ∈ H := by
  have hm : a * (x * b * x⁻¹) ∈ H := by
    rw [hbx]
    exact H.mul_mem ha hb
  rw [heq]
  simpa only [mul_assoc] using hm
""" + finish
    cases = [
        ("commuting_control", commuting, True),
        ("normalizer_extension", normalizer, True),
        ("missing_hypothesis_control", "exact hx", False),
        ("commuting_control", "sorry", False),
        ("commuting_control", "exact hx", False),
        ("normalizer_extension", "axiom fabricated : False", False),
    ]
    return [{"probe": name, "text": "```lean4\n" + body + "\n```",
             "expected_accepted": expected, "origin": "assistant-authored preflight"}
            for name, body, expected in cases]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_dir", type=Path)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--preflight", action="store_true",
                        help="Check authored positive/negative controls; no GPU proposals")
    args = parser.parse_args()
    if not str(args.run_dir.resolve()).startswith("/projects/standard/"):
        raise ValueError("Verification requires run storage under /projects/standard/")
    checked = args.run_dir / "verification"
    checked.mkdir(exist_ok=True)
    libraries = [args.project / ".lake/build/lib/lean"]
    libraries += sorted((args.project / ".lake/packages").glob("*/.lake/build/lib/lean"))
    if not (args.project / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").exists():
        raise RuntimeError("A warm Mathlib build is required")
    # LEAN_PATH is Lean's required library interface. Do not invoke Lake or build.
    lean_env = dict(os.environ, LEAN_PATH=":".join(str(path) for path in libraries))
    (checked / "false-control-witness.json").write_text(json.dumps(false_control_witness(), indent=2) + "\n")
    if args.preflight:
        rows = preflight_rows()
        (checked / "authored-controls.json").write_text(json.dumps(rows, indent=2) + "\n")
    else:
        rows = [json.loads(line) for line in (args.run_dir / "output/proposals.jsonl").read_text().splitlines()]

    def verify(item):
        number, row = item
        result = {"index": number, "probe": row["probe"], "accepted": False}
        tick = time.monotonic()
        try:
            body = tactic_body(row["text"])
            source = (LEAN_IMPORTS + "set_option maxHeartbeats 400000\n\n" +
                      PROBES[row["probe"]]["statement"] + "\n" +
                      "\n".join("  " + line for line in body.splitlines()) +
                      "\n\n#print axioms bh_probe\n")
            path = checked / ("proposal_" + str(number) + ".lean")
            path.write_text(source)
            proc = subprocess.run([str(args.lean), "-j1", "-M2048", str(path)],
                                  cwd=args.project, env=lean_env,
                                  capture_output=True, text=True, timeout=20)
            output = proc.stdout + proc.stderr
            (checked / ("proposal_" + str(number) + ".log")).write_text(output)
            match = re.search(r"'bh_probe' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
            no_axioms = "'bh_probe' does not depend on any axioms" in output
            axioms = set(a.strip() for a in match.group(1).split(",") if a.strip()) if match else set()
            valid_axioms = no_axioms or (match is not None and axioms <= {"propext", "Classical.choice", "Quot.sound"})
            result["accepted"] = proc.returncode == 0 and valid_axioms and "sorry" not in output.lower()
            result["axioms"] = sorted(axioms)
            result["returncode"] = proc.returncode
            if not result["accepted"]:
                result["diagnostic"] = output[-1500:]
        except (ValueError, subprocess.TimeoutExpired) as error:
            result["diagnostic"] = str(error)
        result["seconds"] = time.monotonic() - tick
        return result

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(verify, enumerate(rows)))
    summary = {name: {"proposals": sum(r["probe"] == name for r in results),
                      "accepted": sum(r["probe"] == name and r["accepted"] for r in results)}
               for name in PROBES}
    (checked / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    (checked / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    if summary["missing_hypothesis_control"]["accepted"]:
        raise RuntimeError("False control accepted: invalidate this entire verification run")
    if args.preflight:
        mismatches = [r["index"] for r in results
                      if r["accepted"] != rows[r["index"]]["expected_accepted"]]
        if mismatches:
            raise RuntimeError(f"Authored preflight failed at control indices {mismatches}")


if __name__ == "__main__":
    main()
