"""Seeds at the minimax coboundary optimum: e^{i theta_s} times the metaplectic models (theta from abelian_check)."""
import json, numpy as np
th = 2*np.pi*np.array([-0.0098, -0.0098, -0.0003, 0.0002, 0.0098, 0.0098, 0.0004, 0.0])
def load(fn):
    J=json.load(open(fn)); a=np.array(J["seed"]); return (a[:,:,0]+1j*a[:,:,1]).reshape(8,J["d"],J["d"])
def dump(V, fn):
    json.dump({"seed": [[[float(z.real), float(z.imag)] for z in row] for M in V for row in M], "d": V.shape[1]}, open(fn,"w"))
for fn in ["seed_theta_d4.json", "seed_theta_d10.json", "seed_theta_4x3_d12.json", "seed_theta_10p10_d20.json", "seed_theta_4p4_d8.json", "seed_theta_10p4_d14.json"]:
    S = load(fn); dump(np.stack([np.exp(1j*th[i])*S[i] for i in range(8)]), fn.replace(".json", "_abmin.json"))
print("abmin seeds written")
