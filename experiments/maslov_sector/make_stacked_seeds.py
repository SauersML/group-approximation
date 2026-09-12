import json, numpy as np
J=json.load(open("seed_theta_d10.json")); a=np.array(J["seed"]); U=(a[:,:,0]+1j*a[:,:,1]).reshape(8,10,10)
def dump(V, fn):
    d=V.shape[1]; json.dump({"seed": [[[float(z.real), float(z.imag)] for z in row] for M in V for row in M], "d": d}, open(fn,"w"))
dump(np.stack([np.kron(U[i], np.eye(2)) for i in range(8)]), "seed_theta_x2_d20.json")
dump(np.stack([np.kron(np.eye(2), U[i]) for i in range(8)]), "seed_theta_sum2_d20.json")
dump(np.stack([np.kron(U[i], np.eye(3)) for i in range(8)]), "seed_theta_x3_d30.json")
print("stacked seeds written")
