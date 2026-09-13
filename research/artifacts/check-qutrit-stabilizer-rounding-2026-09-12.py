# Model test of Theorem SR_d for d=3:
#   stab_max(K) >= lambda_max(K) - C_3 (W - lambda_max(K)),  C_3 = 8/sin^2(pi/3) - 1
# on random Hermitian Weyl sums over n<=2 qutrits, with exhaustive stabilizer-state
# enumeration (BFS under Fourier, phase and SUM gates). Reports violations (must be
# zero), the stabilizer counts (expected 12 and 360), and the largest ratio
# (lambda_max - stab_max)/F.
import itertools, math, random
import numpy as np

d = 3
w = np.exp(2j*math.pi/d)
Xq = np.roll(np.eye(d), 1, axis=0).astype(complex)          # X|j> = |j+1>
Zq = np.diag([w**j for j in range(d)])                      # Z|j> = w^j |j>
I3 = np.eye(d, dtype=complex)

def kron_all(ms):
    out = ms[0]
    for m in ms[1:]:
        out = np.kron(out, m)
    return out

def weyl(a, b):
    return kron_all([np.linalg.matrix_power(Xq, ai) @ np.linalg.matrix_power(Zq, bi) for ai, bi in zip(a, b)])

def stabilizer_states(n):
    F = np.array([[w**(j*k) for k in range(d)] for j in range(d)], dtype=complex).T / math.sqrt(d)
    P = np.diag([1, 1, w])
    gates = []
    for q in range(n):
        for g in (F, P):
            ops = [I3]*n; ops[q] = g; gates.append(kron_all(ops))
    dim = d**n
    for c in range(n):
        for t in range(n):
            if c == t: continue
            U = np.zeros((dim, dim), dtype=complex)
            for idx in range(dim):
                digs = [(idx // d**(n-1-k)) % d for k in range(n)]
                digs[t] = (digs[t] + digs[c]) % d
                idx2 = sum(dg * d**(n-1-k) for k, dg in enumerate(digs))
                U[idx2, idx] = 1
            gates.append(U)
    def canon(v):
        k = int(np.argmax(np.abs(v) > 1e-9))
        v = v * (abs(v[k]) / v[k])
        return tuple(np.round(v, 6)), v
    start = np.zeros(dim, dtype=complex); start[0] = 1
    key, v = canon(start); seen = {key: v}; frontier = [v]
    while frontier:
        nxt = []
        for v in frontier:
            for U in gates:
                k2, u = canon(U @ v)
                if k2 not in seen:
                    seen[k2] = u; nxt.append(u)
        frontier = nxt
    return list(seen.values())

def run(n, trials, seed):
    rng = random.Random(seed)
    labels = [(a, b) for a in itertools.product(range(d), repeat=n) for b in itertools.product(range(d), repeat=n)]
    mats = {lab: weyl(*lab) for lab in labels}
    stabs = stabilizer_states(n)
    C3 = 8/math.sin(math.pi/d)**2 - 1
    worst = 0.0; worst_inst = None; viol = 0
    for tr in range(trials):
        m = rng.randint(1, 6)
        terms = []
        for _ in range(m):
            lab = rng.choice(labels)
            c = complex(rng.uniform(-1, 1), rng.uniform(-1, 1))
            if rng.random() < 0.5:
                c = 1.0 + 0.1*c   # bias toward low frustration
            terms.append((lab, c))
        # Hermitian: K = sum c g + conj(c) g^dagger, weight counts both halves
        K = sum(c*mats[lab] + np.conj(c)*mats[lab].conj().T for lab, c in terms)
        W = sum(2*abs(c) for lab, c in terms)
        lam = float(np.linalg.eigvalsh(K)[-1])
        stab = max(float(np.real(np.vdot(v, K @ v))) for v in stabs)
        Fr = W - lam
        if stab < lam - C3*Fr - 1e-9:
            viol += 1
        if Fr > 1e-9:
            r = (lam - stab)/Fr
            if r > worst:
                worst = r; worst_inst = (terms, lam, stab, W)
    print(f"d=3 n={n} stabilizer_states={len(stabs)} trials={trials} violations={viol} worst_ratio={worst:.6f} C3={C3:.4f}")
    if worst_inst:
        print("  worst instance:", worst_inst)

if __name__ == '__main__':
    for n, trials in ((1, 3000), (2, 1500)):
        run(n, trials, 777 + n)
    print("DONE_QUTRIT")
