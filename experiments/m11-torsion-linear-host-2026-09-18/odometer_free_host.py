#!/usr/bin/env python3
"""Checks for the odometer-free candidate R'' = <M_11, b, c> with c = (c, b alpha, 1, ..., 1).

Same conventions and exact word solver as torsion_linear_host.py (imported). The letter c now
has section c at 1 and the two-letter word b alpha at 2; reduced sections never have more
non-finitary letters than the word, so the section closure stays finite.
Checks:
 (1) u = c b^-1 = (u, b, beta^-1, 1, ...) has u^55 = 1, hence 55[c] = 55[b] = 0 in H_1;
 (2) the orbit-return certificate that b*alpha, b*beta, b*alpha*beta have infinite order;
 (3) c and b alpha are nontrivial in many powers (consistent with (2));
 (4) with the letter u = (u, b, beta^-1, 1, ...): the mass identities
     sum_x e_u(w|_x) = e_u(w) and sum_x e_b(w|_x) = e_b(w) + e_u(w) on all words of length <= 5;
 (5) every stable (word, point) pair over {b, u}^+-1 of length <= 6 reads each letter at point 1
     or reads a u-letter at point 2 (the only non-finitary letter sections);
 (6) census: every trivial reduced word of length <= 6 over {b, u, alpha, beta}^+-1 has
     e_u = e_b = 0 mod 55, as the characters of the claim require.
"""
import itertools
import torsion_linear_host as T
from torsion_linear_host import mul, inv, ID, ALPHA, BETA, B, Bi, C, Ci, Pa, Pai, Pb, Pbi, is_trivial, raw_section, reduce

T.SEC['c'] = {0: ('c', 1), 1: [('b', 1), ('p', ALPHA)]}
_old = T.letter_section
def letter_section(l, y):
    if l[0] == 'c':
        # c has trivial root: (c^-1)|_y = (c|_y)^-1
        s = T.SEC['c'].get(y)
        if s is None: return None
        if isinstance(s, list):
            return s if l[1] == 1 else T.winv(tuple(s))
        return s if l[1] == 1 else (s[0], -s[1])
    return _old(l, y)
def raw_section2(w, x):
    out = []; y = x
    for l in w:
        t = letter_section(l, y)
        if t is not None:
            if isinstance(t, (list, tuple)) and t and isinstance(t[0], tuple): out.extend(t)
            else: out.append(t)
        y = T.letter_root(l)[y]
    return tuple(out)
T.raw_section = raw_section2

def order_certificate(start):
    """iterate pi -> rho where (b pi)^L|_1 = b rho, L = length of the pi-cycle through 1."""
    BSEC = {1: ALPHA, 2: BETA}
    pi = start; seen = {}; seq = []
    while pi not in seen:
        seen[pi] = len(seq)
        rho = ID; y = pi[0]; L = 1
        while y != 0:
            if y in BSEC: rho = mul(rho, BSEC[y])
            y = pi[y]; L += 1
        seq.append((pi, L)); pi = rho
    s = seen[pi]
    return seq, s

def main():
    U = (C, Bi) * 55
    u = (C, Bi)
    print("(1) sections of u = c b^-1:", [reduce(T.raw_section(u, x)) for x in range(3)])
    for n, exp in [(55, True), (11, False), (5, False)]:
        got = is_trivial(u * n); print(f"(1) u^{n} = 1: {got} (expected {exp})"); assert got == exp
    got = is_trivial((B,) * 55); print("(1) b^55 = 1:", got); assert got
    names = {ALPHA: 'alpha', BETA: 'beta', mul(ALPHA, BETA): 'alpha beta'}
    seq, s = order_certificate(ALPHA)
    prod = 1
    for i, (p, L) in enumerate(seq):
        print(f"(2) step {i}: b*{names.get(p, p)}  cycle length of 1: {L}")
        if i >= s: prod *= L
    print(f"(2) T-orbit of alpha enters a {len(seq) - s}-cycle at step {s}; product of cycle lengths on it = {prod} > 1")
    assert prod > 1
    for n in [11, 55, 121, 275]:
        got = is_trivial((C,) * n); print(f"(3) c^{n} = 1: {got} (expected False)"); assert not got
        got = is_trivial((B, Pa) * n); print(f"(3) (b alpha)^{n} = 1: {got} (expected False)"); assert not got
    got = is_trivial((Bi, Ci, B, C)); print("(3) [b, c] = 1:", got, "(expected False)"); assert not got
    # (4)-(6): the generator u as a letter
    T.ROOT['u'] = ID
    T.SEC['u'] = {0: ('u', 1), 1: ('b', 1), 2: ('p', inv(BETA))}
    Uu, Ui = ('u', 1), ('u', -1)
    ex = T.ex
    assert is_trivial(T.winv((Uu,)) + (C, Bi)), "u = c b^-1"
    alph = [B, Bi, Uu, Ui, Pa, Pai, Pb, Pbi]; cnt = 0
    for L in range(1, 6):
        for w in itertools.product(alph, repeat=L):
            secs = [T.raw_section(w, x) for x in range(11)]
            assert sum(ex(t, 'u') for t in secs) == ex(w, 'u')
            assert sum(ex(t, 'b') for t in secs) == ex(w, 'b') + ex(w, 'u')
            assert all(T.nf(t) <= T.nf(w) for t in secs)
            cnt += 1
    print(f"(4) mass identities for e_u and e_b (+ e_u) hold on all {cnt} words of length <= 5")
    nst = 0
    for L in range(1, 7):
        for w in itertools.product([B, Bi, Uu, Ui], repeat=L):
            for x in range(11):
                t = T.raw_section(w, x)
                if T.nf(t) == L:
                    nst += 1
                    assert x == 0 or (x == 1 and all(l[0] == 'u' for l in w)), (w, x)
    print(f"(5) {nst} stable pairs up to length 6: letters read at point 1, or all-u words read at point 2")
    rel = 0; bad = 0; nz = 0
    for L in range(1, 7):
        for w in itertools.product(alph, repeat=L):
            if reduce(w) != w or T.root(w) != ID: continue
            if is_trivial(w):
                rel += 1
                if ex(w, 'u') or ex(w, 'b'): nz += 1
                if ex(w, 'u') % 55 or ex(w, 'b') % 55: bad += 1; print("   bad relation", w)
    print(f"(6) trivial reduced words of length <= 6: {rel} ({nz} with nonzero exponents); violating mod 55: {bad}")
    assert bad == 0
    print("done")

if __name__ == "__main__":
    main()
