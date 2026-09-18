"""Print the Ramsey profile table from the cegar_*.json / certify_*.json / third_barrier_*.json
outputs in this directory.  usage: python3 summarize.py
"""
import glob
import json
import re

for path in sorted(glob.glob("cegar_*_n*.json"), key=lambda p: (p.split("_")[1], int(re.findall(r"n(\d+)", p)[0]))):
    r = json.load(open(path))
    w = r.get("witness") or {}
    print(f"{r['group']:>3} n={r['n']:>2} ball={r['ball']:>7} rho<= {r['rho_upper_exact']:>10} "
          f"LB~{r['rho_lower_approx']:.6f} it={r['iterations']} t={r['seconds']}s "
          f"witness={w.get('collection')}")
for path in sorted(glob.glob("certify_*.json")):
    r = json.load(open(path))
    print(path, {k: r[k] for k in r if k not in ("lambda_exact", "family")})
