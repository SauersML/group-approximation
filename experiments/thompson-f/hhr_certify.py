import json, re, sys
sys.path.insert(0, "/scratch.global/sauer354/thompson-f-cogrowth")
import cogrowth_exact as ce
tex = open("/scratch.global/sauer354/thompson-f-lit/xhhr/ThompsonF.tex").read()
blk = tex.split("(Case 2).")[1].split("\\end{tabular}")[0]
rows = []
for line in blk.splitlines():
    parts = [p.strip() for p in line.replace("\\\\", "").split("&")]
    if len(parts) == 5 and parts[0].isdigit():
        rows.append([int(p) for p in parts])
ours = [1, 4, 28, 232, 2092, 19884, 196096, 1988452, 20612364, 217561120, 2331456068,
        25311956784, 277937245744, 3082543843552, 34493827011868, 389093033592912]
c2 = [1] + [r[4] for r in rows]
out = {"rows_parsed": len(rows), "max_n": rows[-1][0],
       "agree_with_repo_out15_j_le_15": c2[:16] == ours,
       "hhr_c2_16_to_24": c2[16:]}
for N in (15, 23, 24):
    cert = ce.certificate(c2[:N + 1])
    out["cert_N%d" % N] = {k: cert[k] for k in ("k", "theta", "p_k_at_theta_negative", "rho_lower_bound", "rho_lower_bound_float")}
print(json.dumps(out, indent=1))
