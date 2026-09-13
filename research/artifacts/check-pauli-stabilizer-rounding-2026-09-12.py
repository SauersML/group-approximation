# Model test of Theorem SR: stab_max(H) >= lambda_max(H) - (1+sqrt2)(W - lambda_max(H))
# on random Pauli sums over n<=3 qubits, with exhaustive stabilizer-state enumeration.
# Reports violations (must be zero) and the largest observed ratio (lambda-stab)/F.
import itertools, math, random, sys
import numpy as np

I2 = np.eye(2, dtype=complex); X = np.array([[0,1],[1,0]], dtype=complex)
Y = np.array([[0,-1j],[1j,0]], dtype=complex); Z = np.array([[1,0],[0,-1]], dtype=complex)
PAU = {'I': I2, 'X': X, 'Y': Y, 'Z': Z}

def kron_all(ms):
    out = ms[0]
    for m in ms[1:]:
        out = np.kron(out, m)
    return out

def pauli(s):
    return kron_all([PAU[c] for c in s])

def stabilizer_states(n):
    # BFS over states reachable from |0...0> by H, S, CNOT; canonical global phase.
    Hg = np.array([[1,1],[1,-1]], dtype=complex)/math.sqrt(2); Sg = np.diag([1,1j])
    gates = []
    for q in range(n):
        for g in (Hg, Sg):
            ops = [I2]*n; ops[q] = g; gates.append(kron_all(ops))
    dim = 2**n
    for c in range(n):
        for t in range(n):
            if c == t: continue
            U = np.zeros((dim,dim), dtype=complex)
            for b in range(dim):
                bits = [(b >> (n-1-k)) & 1 for k in range(n)]
                if bits[c]: bits[t] ^= 1
                b2 = sum(bit << (n-1-k) for k, bit in enumerate(bits))
                U[b2, b] = 1
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
                k2, w = canon(U @ v)
                if k2 not in seen:
                    seen[k2] = w; nxt.append(w)
        frontier = nxt
    return list(seen.values())

def run(n, trials, seed):
    rng = random.Random(seed)
    labels = [''.join(p) for p in itertools.product('IXYZ', repeat=n)]
    mats = {s: pauli(s) for s in labels}
    stabs = stabilizer_states(n)
    worst = 0.0; worst_inst = None; viol = 0
    for tr in range(trials):
        m = rng.randint(1, min(8, len(labels)))
        terms = [(rng.choice(labels), rng.uniform(-1, 1)) for _ in range(m)]
        if rng.random() < 0.5:  # bias toward low-frustration instances
            base = [(rng.choice(labels), 1.0) for _ in range(rng.randint(1, 4))]
            terms = base + [(s, 0.2*b) for s, b in terms]
        H = sum(b*mats[s] for s, b in terms)
        W = sum(abs(b) for s, b in terms)
        lam = float(np.linalg.eigvalsh(H)[-1])
        stab = max(float(np.real(np.vdot(v, H @ v))) for v in stabs)
        F = W - lam
        if stab < lam - (1+math.sqrt(2))*F - 1e-9:
            viol += 1
        if F > 1e-9:
            r = (lam - stab)/F
            if r > worst:
                worst = r; worst_inst = (terms, lam, stab, W)
    print(f"n={n} stabilizer_states={len(stabs)} trials={trials} violations={viol} worst_ratio={worst:.6f}")
    if worst_inst:
        print("  worst instance:", worst_inst)

if __name__ == '__main__':
    for n, trials in ((1, 3000), (2, 3000), (3, 1500)):
        run(n, trials, 12345 + n)
    print("DONE_SRCHECK")
