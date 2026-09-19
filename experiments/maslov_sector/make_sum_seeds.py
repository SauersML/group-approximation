import json, numpy as np, sys
def load(fn):
    J=json.load(open(fn)); a=np.array(J["seed"]); return (a[:,:,0]+1j*a[:,:,1]).reshape(8,J["d"],J["d"])
def dump(V, fn):
    json.dump({"seed": [[[float(z.real), float(z.imag)] for z in row] for M in V for row in M], "d": V.shape[1]}, open(fn,"w"))
def dsum(A, B):
    d1, d2 = A.shape[1], B.shape[1]; out = np.zeros((8, d1+d2, d1+d2), dtype=complex)
    for i in range(8): out[i,:d1,:d1] = A[i]; out[i,d1:,d1:] = B[i]
    return out
T10 = load("seed_theta_d10.json"); T4 = load("seed_theta_d4.json")
dump(dsum(T4, T4), "seed_theta_4p4_d8.json")
dump(dsum(T10, T4), "seed_theta_10p4_d14.json")
dump(dsum(T10, T10), "seed_theta_10p10_d20.json")
dump(dsum(dsum(T4, T4), T4), "seed_theta_4x3_d12.json")
print("sum seeds written")
