#!/usr/bin/env python3
"""Checks for donor-covering-types-give-nonsurjunctive-size-progressions.

1. Arithmetic criterion (item 3 of the claim): for z >= 0, b >= 1 there is j with
   2^j > z and 2^j = z (mod b)  iff  2^v | z and z/2^v lies in the cyclic subgroup <2> of
   (Z/b')^x (or b' = 1), where b = 2^v b' with b' odd.  Brute force vs criterion.
2. Tag lift (item 1): over G = C_n, for donor-covering rules tau on L = Z + B with memory
   M = {0,1}, the lift Phi on C = Z + B x C_t (|C| = z + b t) satisfies sigma o Phi = tau o sigma,
   commutes with the fibre action and with translation, and is injective iff tau is.
   Strictness cannot be tested on finite groups: this checks the algebra only.
3. Prints the power-residue types (z, b) with 1 <= z, b <= 12 and the smallest 2^j reached.
"""
import itertools
import random

random.seed(917)


def v2(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def brute(z, b):
    for j in range(0, 2 * b + z.bit_length() + 8):
        if 2 ** j > z and (2 ** j - z) % b == 0:
            return j
    return None


def criterion(z, b):
    v = v2(b)
    bp = b >> v
    if z % (2 ** v):
        return False
    zz = (z >> v) % bp
    if bp == 1:
        return True
    x = 1
    for _ in range(bp):
        if x == zz:
            return True
        x = (2 * x) % bp
    return False


for z in range(0, 80):
    for b in range(1, 80):
        assert (brute(z, b) is not None) == criterion(z, b), (z, b)
print("arithmetic criterion: OK for 0 <= z < 80, 1 <= b < 80")


def donor_rules(z, b, tries):
    """Random rules on L = range(z+b) (0..z-1 rest), memory M = (0, 1), with a donor map."""
    L = z + b
    rules = []
    for _ in range(tries):
        mu, d = {}, {}
        for u in itertools.product(range(L), repeat=2):
            act = [m for m in range(2) if u[m] >= z]
            if act and random.random() < 0.6:
                mu[u] = random.randrange(z, L)
                d[u] = random.choice(act)
            else:
                mu[u] = random.randrange(0, z) if z else random.randrange(z, L)
                if mu[u] >= z:
                    if not act:
                        mu[u] = random.randrange(0, z)
                    else:
                        d[u] = random.choice(act)
        rules.append((mu, d))
    # a structured one: the shift, donor 1
    mu = {u: u[1] for u in itertools.product(range(L), repeat=2)}
    d = {u: 1 for u in mu if mu[u] >= z}
    rules.append((mu, d))
    return rules


def run_tau(mu, l, n):
    return tuple(mu[(l[g], l[(g + 1) % n])] for g in range(n))


def donor_covering(mu, d, z, L, n):
    for l in itertools.product(range(L), repeat=n):
        out = run_tau(mu, l, n)
        relayed = set()
        for g in range(n):
            if out[g] >= z:
                h = (g + d[(l[g], l[(g + 1) % n])]) % n
                if l[h] < z:
                    return False
                relayed.add(h)
        if any(l[h] >= z and h not in relayed for h in range(n)):
            return False
    return True


def lift(mu, d, z, t, n):
    # C = rest 0..z-1, then (beta, phase) encoded as z + beta*t + phase
    def sigma(c):
        return c if c < z else z + (c - z) // t

    def phase(c):
        return (c - z) % t

    def Phi(y):
        l = tuple(sigma(c) for c in y)
        out = []
        for g in range(n):
            u = (l[g], l[(g + 1) % n])
            o = mu[u]
            if o < z:
                out.append(o)
            else:
                h = (g + d[u]) % n
                out.append(z + (o - z) * t + phase(y[h]))
        return tuple(out), sigma, phase
    return Phi, sigma


checked = 0
for (z, b, t, n) in [(2, 1, 3, 3), (1, 2, 2, 3), (3, 1, 5, 3), (2, 2, 3, 3)]:
    L = z + b
    for mu, d in donor_rules(z, b, 400):
        if not donor_covering(mu, d, z, L, n):
            continue
        Phi, sigma = lift(mu, d, z, t, n)
        C = z + b * t
        tau_imgs = {run_tau(mu, l, n) for l in itertools.product(range(L), repeat=n)}
        tau_inj = len(tau_imgs) == L ** n
        imgs = set()
        for y in itertools.product(range(C), repeat=n):
            out = Phi(y)[0]
            imgs.add(out)
            assert tuple(sigma(c) for c in out) == run_tau(mu, tuple(sigma(c) for c in y), n)
            ys = y[1:] + y[:1]
            assert Phi(ys)[0] == out[1:] + out[:1]
            yf = tuple(c if c < z else z + ((c - z) // t) * t + ((c - z) % t + 1) % t for c in y)
            of = tuple(c if c < z else z + ((c - z) // t) * t + ((c - z) % t + 1) % t for c in out)
            assert Phi(yf)[0] == of
        assert (len(imgs) == C ** n) == tau_inj
        checked += 1
print("tag lift: OK on", checked, "donor-covering rules (sizes z + b t)")

print("power-residue types (z, b), 1 <= z, b <= 12, with smallest 2^j:")
for z in range(1, 13):
    row = []
    for b in range(1, 13):
        j = brute(z, b)
        row.append(str(2 ** j) if j is not None else "-")
    print(" z=%2d: " % z + " ".join("%5s" % s for s in row))
