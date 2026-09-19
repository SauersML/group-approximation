"""Exact Farkas vector for the mixed-memory LP of lp_vmem.py (d^- memory rm, d^+ memory rp) from a floating dual,
by the dart shift of farkas_rho.py.  System (lp_vmem.build): A y + B c = e_norm, y, c >= 0.
1. z = round(D * y) on type and pair rows (integers).
2. R_d = max(0, max_k ceil(max{charge(P) : P a k-gon through d} / k)) by exact integer max-plus
   (farkas_rho.dart_max_charge, duck-typed); z'_d = z_d - R_d makes every polygon charge <= 0.
3. z'_norm = min over windows w of -(B_w restricted to the other rows) . z'; then every window charge is <= 0.
4. Independent re-check: verify_farkas_memory.max_polygon_charge(z') <= 0 (max-plus over all typed polygons,
   a superset of lp_memory.polygons) and every window charge <= 0, all in integers below 2^53.
If z'_norm > 0 the mixed LP is infeasible, hence (lp_vmem.py docstring) so is the memory-max(rm, rp) LP of
lp_memory.py: no legal f^m-folded fatgraph over the rose exists, any boundary, so no certificate of this kind.
usage: python3 farkas_vmem.py dump.json [--D D] [--key y|y_rho] [--save cert.json]
       python3 farkas_vmem.py cert.json        (compact integer certificate)
"""
import sys, json
import numpy as np
import lp_vmem as VM
import verify_farkas_memory as VF
import farkas_rho as FR


def main():
    args = sys.argv[1:]
    D, key, save = 10 ** 6, "y", None
    for opt in ("--D", "--key", "--save"):
        if opt in args:
            i = args.index(opt); val = args[i + 1]; del args[i:i + 2]
            if opt == "--D": D = int(val)
            elif opt == "--key": key = val
            else: save = val
    J = json.load(open(args[0]))
    phi, g, TY, maxval = VM.setup(J["phi0"], J["power"], J["rm"], J["rp"])
    assert maxval == 4
    N = TY.N
    nrows0, _, ccols = VM.build(TY, [])
    rN = J["rN"]; assert rN == nrows0
    if "zrows" in J:
        D = int(J["D"])
        z = np.array(J["zrows"], dtype=float)
        zpair = {(a, b): float(v) for a, b, v in J["zpairs"]}
    else:
        y = np.array(J[key])
        z = np.round(y[:rN] * D)
        zpair = {(a, b): float(np.round(y[rw] * D)) if rw < len(y) else 0.0 for a, b, rw in J["prow"]}
        zpair = {k: v for k, v in zpair.items() if v != 0}
    assert len(z) == rN
    mc = FR.dart_max_charge(TY, g, z[:N], zpair)
    R = np.zeros(N)
    for k in (2, 3, 4):
        R = np.maximum(R, np.ceil(mc[k] / k))
    zp = z.copy(); zp[:N] -= R
    assert max(abs(zp).max(), max([abs(v) for v in zpair.values()] + [0])) * 16 < 2 ** 52
    wch = [sum(v * zp[row] for row, v in col.items()) for col in ccols]
    znorm = -max(wch)
    pmax, best = VF.max_polygon_charge(TY, g, 4, zp[:N], zpair)
    wmax = max(w + znorm for w in wch)
    print("phi0", J["phi0"], "m", J["power"], "rm", J["rm"], "rp", J["rp"], "types", N, "windows", len(ccols),
          "D", D, "key", key)
    print("shift: darts with R_d > 0:", int((R > 0).sum()), "max R", float(R.max()))
    print("z'_norm", znorm, "(/D = %.6g)" % (znorm / D), "max window charge", wmax, "max polygon charge", pmax, best)
    ok = znorm > 0 and wmax <= 0 and pmax <= 0
    print("FARKAS", "VERIFIED" if ok else "FAILED", flush=True)
    if save:
        json.dump({"phi0": J["phi0"], "power": J["power"], "rm": J["rm"], "rp": J["rp"], "rN": rN, "D": D,
                   "zrows": [int(v) for v in z], "zpairs": [[int(a), int(b), int(v)] for (a, b), v in zpair.items()],
                   "verified": bool(ok), "znorm": int(znorm)}, open(save, "w"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
