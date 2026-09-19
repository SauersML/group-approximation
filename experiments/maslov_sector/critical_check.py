"""Numerical check of exact-projective-models-are-critical-modulo-coboundaries: at the exact theta models the
Riemannian gradient of the mean-square mod-3 relator energy has no component in traceless directions."""
import sys, numpy as np
src = open("optimize6.py").read().split("best = None")[0]
for seedfn, dd in (("seed_theta_d4.json", 4), ("seed_theta_d10.json", 10)):
    sys.argv = ["optimize6.py", "pres6.json", "3", "seed:" + seedfn, str(dd), "1", "0", "3000", "5", "1", "0", "0.0"]
    exec(src)
    Us = load_seed(seedfn); CU = classes_of(z, maxlen=13)
    e, ms, mu, ml, g = energy_and_grad(Us, CU); gr = tangent(Us, g)
    for i in range(8):
        v = 1j * Us[i]                      # coboundary direction
        a = np.real(np.vdot(v, gr[i])) / np.real(np.vdot(v, v))
        rest = gr[i] - a * v
        print(f"{seedfn} generator {i}: |grad| {np.linalg.norm(gr[i]):.3e}, coboundary coefficient {a:.3e}, traceless remainder {np.linalg.norm(rest):.3e}", flush=True)
