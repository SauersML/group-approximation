import sys, numpy as np
src = open("optimize7.py").read().split("best = None")[0]
sys.argv = ["optimize7.py", "pres6.json", "3", "random", "4", "1", "0", "300", "5", "30", "0", "0.2"]
exec(src)
Us = initial(0.2); CU = classes_of(z, maxlen=13)
e, ms, mu, ml, g = energy_and_grad(Us, CU); gr = tangent(Us, g)
for trial in range(3):
    V = np.stack([Us[i] @ (1j*rand_herm()) for i in range(8)]); h = 1e-5
    ep, *_ = energy_and_grad(retract(Us, h*V), CU); em, *_ = energy_and_grad(retract(Us, -h*V), CU)
    fd = (ep - em) / (2*h); an = sum(np.real(np.vdot(gr[i], V[i])) for i in range(8))
    print(f"trial {trial}: fd {fd:.6e} analytic {an:.6e} ratio {fd/an:.4f}", flush=True)
