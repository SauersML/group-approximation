"""Stacked metaplectic theta seeds (seed_theta_d10.json tensored with I_m) at the minimax coboundary optimum for the
mod-3 sector (phases from abelian_check.py / make_abmin_seeds.py on main).  Writes seed_theta_x{m}_d{10m}_abmin.json.
NUMERICS SEEDS ONLY: exact projective models of the METAPLECTIC class, rescaled; they are not mod-3 sector models."""
import json, sys, numpy as np
th = 2*np.pi*np.array([-0.0098, -0.0098, -0.0003, 0.0002, 0.0098, 0.0098, 0.0004, 0.0])
J = json.load(open("seed_theta_d10.json")); a = np.array(J["seed"]); U = (a[:, :, 0] + 1j*a[:, :, 1]).reshape(8, 10, 10)
def dump(V, fn):
    json.dump({"seed": [[[float(z.real), float(z.imag)] for z in row] for M in V for row in M], "d": V.shape[1]}, open(fn, "w"))
for m in [int(x) for x in sys.argv[1:]] or [2, 3, 4]:
    V = np.stack([np.exp(1j*th[i]) * np.kron(U[i], np.eye(m)) for i in range(8)])
    dump(V, f"seed_theta_x{m}_d{10*m}_abmin.json")
    print("wrote", f"seed_theta_x{m}_d{10*m}_abmin.json", flush=True)
