#!/usr/bin/env python3
"""Word evaluator and exponent-descent checks for R = <M_11, a, b, c> on the 11-ary tree.

Conventions (as in m11-linear-activity-self-replicating-group): right actions,
(x w)^g = x^{pi_g} w^{g|_x},  (gh)|_x = g|_x h|_{x^{pi_g}}.  Letters 0..10 stand for 1..11.
  a = (a, 1, ..., 1) alpha      alpha = (1,2,...,11)
  b = (b, alpha, beta, 1, ...)  beta  = (1,2,3,4,8)(5,10,7,11,6)
  c = (c, a, 1, ..., 1)
A word is a tuple of letters: ('a',e), ('b',e), ('c',e) with e = +-1, or ('p', perm) with perm in M_11.
Triviality is decided exactly by coinduction: reduced sections of a word never have more
non-finitary letters than the word, so the section closure is finite; the word is trivial iff
every word in its closure has trivial root permutation (induction on the level).
"""
import itertools, sys

D = 11
ID = tuple(range(D))
def perm_from_cycles(cycles):
    p = list(range(D))
    for cyc in cycles:
        for i, x in enumerate(cyc):
            p[x - 1] = cyc[(i + 1) % len(cyc)] - 1
    return tuple(p)
def mul(p, q):          # right action: x^(pq) = (x^p)^q
    return tuple(q[p[x]] for x in range(D))
def inv(p):
    r = [0] * D
    for x in range(D): r[p[x]] = x
    return tuple(r)

ALPHA = perm_from_cycles([list(range(1, 12))])
BETA = perm_from_cycles([[1, 2, 3, 4, 8], [5, 10, 7, 11, 6]])
M11_GENS = [ALPHA, tuple(x - 1 for x in [1, 2, 7, 10, 6, 4, 11, 3, 9, 5, 8])]  # GAP: Stab_{M12}(12)

def closure(gens):
    seen = {ID}; frontier = [ID]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = mul(g, s)
                if h not in seen: seen.add(h); nxt.append(h)
        frontier = nxt
    return seen
M11 = closure(M11_GENS)
assert len(M11) == 7920 and BETA in M11

# state table for the positive generators: root permutation and sections (letter or None)
ROOT = {'a': ALPHA, 'b': ID, 'c': ID}
SEC = {'a': {0: ('a', 1)}, 'b': {0: ('b', 1), 1: ('p', ALPHA), 2: ('p', BETA)}, 'c': {0: ('c', 1), 1: ('a', 1)}}

def letter_root(l):
    if l[0] == 'p': return l[1]
    r = ROOT[l[0]]
    return r if l[1] == 1 else inv(r)
def letter_section(l, y):
    """raw section of one letter at point y: a letter or None"""
    if l[0] == 'p': return None
    s, e = l
    if e == 1:
        return SEC[s].get(y)
    y0 = inv(ROOT[s])[y]          # (g^-1)|_y = (g|_{y^{pi^-1}})^-1
    t = SEC[s].get(y0)
    if t is None: return None
    return ('p', inv(t[1])) if t[0] == 'p' else (t[0], -t[1])
def raw_section(w, x):
    out = []; y = x
    for l in w:
        t = letter_section(l, y)
        if t is not None: out.append(t)
        y = letter_root(l)[y]
    return tuple(out)
def root(w):
    p = ID
    for l in w: p = mul(p, letter_root(l))
    return p
def reduce(w):
    out = []
    for l in w:
        if l[0] == 'p':
            if out and out[-1][0] == 'p':
                q = mul(out[-1][1], l[1]); out.pop()
                if q != ID: out.append(('p', q))
            elif l[1] != ID: out.append(l)
        elif out and out[-1][0] == l[0] and out[-1][1] == -l[1]:
            out.pop()
        else:
            out.append(l)
    return tuple(out)
def is_trivial(w, limit=200000):
    start = reduce(w); seen = {start}; stack = [start]
    while stack:
        u = stack.pop()
        if root(u) != ID: return False
        for x in range(D):
            v = reduce(raw_section(u, x))
            if v not in seen:
                seen.add(v); stack.append(v)
                if len(seen) > limit: raise RuntimeError("closure too large")
    return True
def ea(w): return sum(l[1] for l in w if l[0] == 'a')
def ec(w): return sum(l[1] for l in w if l[0] == 'c')
def nf(w): return sum(1 for l in w if l[0] != 'p')

A, Ai, B, Bi, C, Ci = ('a', 1), ('a', -1), ('b', 1), ('b', -1), ('c', 1), ('c', -1)
Pa, Pai, Pb, Pbi = ('p', ALPHA), ('p', inv(ALPHA)), ('p', BETA), ('p', inv(BETA))
def winv(w): return tuple((('p', inv(l[1])) if l[0] == 'p' else (l[0], -l[1])) for l in reversed(w))
def conj(w, p): return (('p', inv(p)),) + w + (('p', p),)

def main():
    print("M_11 order", len(M11), "; alpha, beta in M_11: True")
    # (1) calibration of the solver on known identities and non-identities
    a_at1 = (A, Pai)                                    # a@1 = a alpha^-1
    a_at2 = conj(a_at1, ALPHA)                          # a@2 = alpha^-1 (a@1) alpha
    c_at1 = (C,) + winv(a_at2)                          # c@1 = c (a@2)^-1
    q12 = next(q for q in M11 if q[0] == 0 and q[1] == 1 and q != ID)
    checks = {
        "[a@1, a@2] = 1": (winv(a_at1) + winv(a_at2) + a_at1 + a_at2, True),
        "q^-1 c q = c for q in Stab(1,2)": (conj((C,), q12) + (Ci,), True),
        "[c@1, a@2] = 1": (winv(c_at1) + winv(a_at2) + c_at1 + a_at2, True),
        "a^11 = 1": ((A,) * 11, False),
        "c^11 = 1": ((C,) * 11, False),
        "b^55 = 1": ((B,) * 55, True),
        "b^11 = 1": ((B,) * 11, False),
        "[b, c] = 1": ((Bi, Ci, B, C), False),
    }
    for name, (w, expect) in checks.items():
        got = is_trivial(w)
        print(f"(1) {name}: {got}  (expected {expect})"); assert got == expect
    # (2) the section-mass identity  sum_x e_a(w|_x) = e_a(w) + e_c(w),  sum_x e_c(w|_x) = e_c(w)
    #     and |w|_x| <= nf(w), on all words of length <= 5 over {a,b,c,alpha,beta}^+-1
    alph = [A, Ai, B, Bi, C, Ci, Pa, Pai, Pb, Pbi]
    cnt = 0
    for L in range(1, 6):
        for w in itertools.product(alph, repeat=L):
            secs = [raw_section(w, x) for x in range(D)]
            assert sum(ea(s) for s in secs) == ea(w) + ec(w)
            assert sum(ec(s) for s in secs) == ec(w)
            assert all(len(s) <= nf(w) for s in secs)
            cnt += 1
    print(f"(2) mass identities and length bound hold on all {cnt} words of length <= 5")
    # (3) stable-word lemma: a word over {a,b,c}^+-1 all of whose letters have a non-finitary
    #     section at their point (start point x) has |e_a| <= 1; brute force up to length 7
    nfal = [A, Ai, B, Bi, C, Ci]; worst = 0; nstable = 0
    for L in range(1, 8):
        for w in itertools.product(nfal, repeat=L):
            for x in range(D):
                s = raw_section(w, x)
                if len(s) == L and nf(s) == L:
                    nstable += 1; worst = max(worst, abs(ea(w)))
    print(f"(3) {nstable} stable (word, point) pairs up to length 7; max |e_a| = {worst}"); assert worst <= 1
    # (4) exhaustive relation census: all reduced words of length <= 6 over {a,b,c,alpha,beta}^+-1
    #     that are trivial in R, with their exponent sums
    rel = 0; bad = 0; seen = set()
    for L in range(1, 7):
        for w in itertools.product(alph, repeat=L):
            if reduce(w) != w or w in seen: continue
            if root(w) != ID: continue
            if is_trivial(w):
                rel += 1
                if ea(w) != 0 or ec(w) != 0: bad += 1; print("   relation with nonzero exponent:", w)
    print(f"(4) trivial reduced words of length <= 6: {rel}; with (e_a, e_c) != (0,0): {bad}"); assert bad == 0
    print("done")

if __name__ == "__main__":
    main()
