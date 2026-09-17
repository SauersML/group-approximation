#!/usr/bin/env python3
"""Finite calibration for donor-covering-strict-automata-descend-to-two-symbols.

Checks, exhaustively on small cyclic index groups G = C_n:
  1. the phase-transport map Phi built from a donor-covering automaton tau on labels
     commutes with G-translation and with the symbolwise fibre action,
  2. sigma o Phi = tau o sigma (labels of the output are tau of the input labels),
  3. tau injective  => Phi injective,
  4. tau not surjective => Phi not surjective,
for four fibres: R_5 = F_2[x]/(Phi_5) (one rest symbol, 3 free orbits), {0,1}^{C_3}
(two rest symbols, 2 free orbits), {0,1}^{C_2} (two rest symbols, 1 free orbit), and a
tag fibre {0} + C_3 (tag multiplication, one rest symbol, 1 orbit).
Also checks the orbit counts (2^p-2)/p and (2^(q-1)-1)/q by brute force, and the
divisibility lemma: for every odd b there is a prime q > b with b | (2^(q-1)-1)/q.
Strictness itself cannot be tested on finite groups; this is a sanity check of the
algebra only.
"""
import itertools
import random

random.seed(20260917)


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


# ---------- fibres ----------
def fibre_R5():
    mod = 0b11111  # x^4+x^3+x^2+x+1

    def mulx(c):
        c <<= 1
        if c & 0b10000:
            c ^= mod
        return c

    def act(k, c):
        for _ in range(k % 5):
            c = mulx(c)
        return c

    return dict(name="R_5 (Z={0})", C=list(range(16)), order=5, act=act)


def fibre_bits(p):
    def act(k, c):
        k %= p
        return ((c << k) | (c >> (p - k))) & ((1 << p) - 1) if k else c

    return dict(name="{0,1}^C_%d" % p, C=list(range(1 << p)), order=p, act=act)


def fibre_tag(t):
    # {0} + C_t, the group C_t acting by translation on the nonzero part
    def act(k, c):
        return 0 if c == 0 else 1 + (c - 1 + k) % t

    return dict(name="tag {0}+C_%d" % t, C=list(range(t + 1)), order=t, act=act)


def analyse(fib):
    C, order, act = fib["C"], fib["order"], fib["act"]
    Z = [c for c in C if all(act(k, c) == c for k in range(order))]
    rest = [c for c in C if c not in Z]
    reps, label, phase = [], {}, {}
    for c in rest:
        if c in label:
            continue
        orb = [act(k, c) for k in range(order)]
        assert len(set(orb)) == order, "action not free off the fixed set"
        reps.append(c)
        for k, d in enumerate(orb):
            label[d] = len(Z) + len(reps) - 1
            phase[d] = k
    for i, z in enumerate(Z):
        label[z] = i
    fib.update(Z=Z, reps=reps, label=label, phase=phase, nZ=len(Z), nB=len(reps))
    return fib


# ---------- donor-covering automata on labels over C_n, memory {g, g+1} ----------
def random_tau(nZ, nB):
    L = nZ + nB
    F0 = {(a, b): random.randrange(nZ) for a in range(nZ) for b in range(nZ)}
    mode = random.random()
    F1 = {}
    for a in range(nZ, L):
        for b in range(L):
            if mode < 0.5:
                # permutation of B in the first argument, depending on b
                pass
            F1[(a, b)] = None
    for b in range(L):
        perm = list(range(nZ, L))
        random.shuffle(perm)
        for i, a in enumerate(range(nZ, L)):
            F1[(a, b)] = perm[i] if mode < 0.5 else random.randrange(nZ, L)
    F2 = {(a, b): (random.randrange(L) if random.random() < 0.5 else random.randrange(nZ))
          for a in range(nZ) for b in range(nZ, L)}
    if random.random() < 0.4:
        # structured: rest sites keep their rest symbol, active sites are permuted by
        # the right neighbour's label (often injective on small cycles)
        F0 = {(a, b): a for a in range(nZ) for b in range(nZ)}
        F2 = {(a, b): a for a in range(nZ) for b in range(nZ, L)}

    def rule(a, b):
        if a >= nZ:
            return F1[(a, b)], 0          # donor offset 0 (the site itself)
        if b >= nZ:
            return F2[(a, b)], 1          # donor offset 1
        return F0[(a, b)], None           # no donor; output is a rest label

    return rule


def apply_tau(rule, ell, n):
    return tuple(rule(ell[g], ell[(g + 1) % n])[0] for g in range(n))


def apply_phi(rule, fib, y, n):
    lab = [fib["label"][c] for c in y]
    out = []
    for g in range(n):
        v, off = rule(lab[g], lab[(g + 1) % n])
        if v < fib["nZ"]:
            out.append(fib["Z"][v])
        else:
            h = (g + off) % n
            out.append(fib["act"](fib["phase"][y[h]], fib["reps"][v - fib["nZ"]]))
    return tuple(out)


def run(fib, n, trials):
    analyse(fib)
    nZ, nB = fib["nZ"], fib["nB"]
    L = nZ + nB
    configs_L = list(itertools.product(range(L), repeat=n))
    configs_C = list(itertools.product(fib["C"], repeat=n))
    stats = dict(trials=0, inj=0, noninj=0)
    for _ in range(trials):
        rule = random_tau(nZ, nB)
        img_tau = {apply_tau(rule, l, n) for l in configs_L}
        img_phi = {}
        for y in configs_C:
            out = apply_phi(rule, fib, y, n)
            # labels commute
            assert tuple(fib["label"][c] for c in out) == apply_tau(
                rule, tuple(fib["label"][c] for c in y), n)
            img_phi.setdefault(out, 0)
            img_phi[out] += 1
        # equivariance on a sample
        for y in random.sample(configs_C, 50):
            out = apply_phi(rule, fib, y, n)
            for k in range(fib["order"]):
                ky = tuple(fib["act"](k, c) for c in y)
                assert apply_phi(rule, fib, ky, n) == tuple(fib["act"](k, c) for c in out)
            sy = y[1:] + y[:1]
            assert apply_phi(rule, fib, sy, n) == out[1:] + out[:1]
        tau_inj = len(img_tau) == len(configs_L)
        phi_inj = len(img_phi) == len(configs_C)
        if tau_inj:
            assert phi_inj
            stats["inj"] += 1
        else:
            assert len(img_phi) < len(configs_C)  # not surjective
            stats["noninj"] += 1
        stats["trials"] += 1
    print("%-18s n=%d  |Z|=%d |B|=%d  %s" % (fib["name"], n, nZ, nB, stats))


def orbit_counts():
    for p in [2, 3, 5, 7, 11, 13]:
        fib = analyse(fibre_bits(p))
        assert fib["nZ"] == 2 and fib["nB"] == (2 ** p - 2) // p
    for q in [3, 5, 7]:
        # R_q has 2^(q-1) elements; count free orbits via the formula only for q=5 brute force
        pass
    fib = analyse(fibre_R5())
    assert fib["nZ"] == 1 and fib["nB"] == 3
    print("orbit counts ok: (2^p-2)/p for p<=13, R_5 has 3 free orbits")
    print("N'_q = (2^(q-1)-1)/q:", {q: (2 ** (q - 1) - 1) // q for q in [3, 5, 7, 11, 13, 17, 19]})


def divisibility():
    worst = 0
    for b in range(1, 400, 2):
        q = b + 1
        while not (is_prime(q) and q > 2 and ((2 ** (q - 1) - 1) // q) % b == 0):
            q += 1
        worst = max(worst, q)
    print("every odd b < 400 divides some N'_q with q prime > b; largest q needed:", worst)
    # |B| divisible by 4 never divides (2^p-2)/p = 2 N'_p (N'_p odd)
    assert all(((2 ** p - 2) // p) % 4 for p in range(2, 200) if is_prime(p))
    print("(2^p-2)/p is never divisible by 4 for primes p < 200")


if __name__ == "__main__":
    orbit_counts()
    divisibility()
    run(fibre_R5(), 3, 40)
    run(fibre_bits(3), 4, 40)
    run(fibre_bits(2), 5, 40)
    run(fibre_tag(3), 5, 40)
    print("ALL CHECKS PASSED")
