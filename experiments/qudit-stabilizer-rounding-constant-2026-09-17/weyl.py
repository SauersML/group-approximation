"""Weyl operators and stabilizer states for n qudits of odd prime dimension d.
D(a,b) = omega^(2^{-1} a.b) X^a Z^b, so D^d = I and D(-v) = D(v)^dagger."""
import itertools
import numpy as np

def omega(d):
    return np.exp(2j * np.pi / d)

def weyl_ops(d, n):
    """returns list of vectors v=(a,b) in F_d^{2n} (nonzero) and matrices D(v)."""
    w = omega(d); inv2 = pow(2, -1, d)
    X = np.roll(np.eye(d), 1, axis=0)          # X|j> = |j+1>
    Z = np.diag([w ** j for j in range(d)])
    one = []
    for a in range(d):
        for b in range(d):
            one.append(((a, b), w ** ((inv2 * a * b) % d) * np.linalg.matrix_power(X, a) @ np.linalg.matrix_power(Z, b)))
    vecs, mats = [], []
    for combo in itertools.product(range(d * d), repeat=n):
        v = []; M = np.eye(1)
        for c in combo:
            (a, b), m = one[c]; M = np.kron(M, m); v.append((a, b))
        a = tuple(x[0] for x in v); b = tuple(x[1] for x in v)
        if any(a) or any(b):
            vecs.append(a + b); mats.append(M)
    return vecs, np.array(mats)

def pair_reps(d, n, vecs):
    """one representative index per pair {v,-v}, and the map v-> index of -v."""
    idx = {v: i for i, v in enumerate(vecs)}
    neg = [idx[tuple((-x) % d for x in v)] for v in vecs]
    reps = [i for i in range(len(vecs)) if i < neg[i]]
    return reps, neg

def stabilizer_states(d, n):
    """orbit of |0..0> under local F, P, X, Z and CSUM gates; returns array (N, d^n)."""
    w = omega(d); inv2 = pow(2, -1, d)
    F = np.array([[w ** (j * k) for k in range(d)] for j in range(d)]) / np.sqrt(d)
    P = np.diag([w ** ((inv2 * j * j) % d) for j in range(d)])
    X = np.roll(np.eye(d), 1, axis=0)
    gates1 = [F, P, X]
    D = d ** n; gens = []
    for q in range(n):
        for g in gates1:
            M = np.eye(1)
            for r in range(n):
                M = np.kron(M, g if r == q else np.eye(d))
            gens.append(M)
    for q in range(n):
        for r in range(n):
            if q != r:
                M = np.zeros((D, D))
                for s in itertools.product(range(d), repeat=n):
                    t = list(s); t[r] = (t[r] + t[q]) % d
                    i = int(np.ravel_multi_index(s, (d,) * n)); j = int(np.ravel_multi_index(tuple(t), (d,) * n))
                    M[j, i] = 1
                gens.append(M)
    def key(v):
        k = np.argmax(np.abs(v) > 1e-9); v = v * np.conj(v[k]) / abs(v[k])
        return tuple(np.round(v.real, 6) + 0.0) + tuple(np.round(v.imag, 6) + 0.0)
    s0 = np.zeros(D, complex); s0[0] = 1
    seen = {key(s0): s0}; frontier = [s0]
    while frontier:
        nxt = []
        for s in frontier:
            for g in gens:
                t = g @ s; k = key(t)
                if k not in seen:
                    seen[k] = t; nxt.append(t)
        frontier = nxt
    return np.array(list(seen.values()))

def expectations(states, mats):
    """E[phi, v] = <phi|D(v)|phi>"""
    return np.einsum('si,vij,sj->sv', np.conj(states), mats, states)

if __name__ == '__main__':
    for d, n in [(3, 1), (3, 2), (5, 1), (7, 1)]:
        st = stabilizer_states(d, n)
        expect = d ** n * np.prod([d ** k + 1 for k in range(1, n + 1)])
        print(d, n, len(st), expect)
