"""Checks for thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3.  Run on MSI (conda/python3, sympy).

1. Coset enumeration: <a,b | a^2, b^3, (ab)^4> has order 24 and <a,c | a^2, c^2, (ac)^3> has order 6.
2. Exact, in V with the right action by prefix replacement, a = (00 01), b = (01 10 11), c = (1 00):
   a, b permute the cones Q = {00,01,10,11} and generate 24 permutations of Q, with ab = (00 10 11 01);
   a, c permute the cones P = {00,01,1} and generate 6 permutations of P, with ac = (00 01 1).
3. Sanity only (triviality is Bleak--Quick's): the eight words of (2.4), c^2 and (ac)^3 fix 4000
   random binary strings of length 64.
"""
import random
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup

F, x, y = free_group("x y")
print("order <a,b | a^2,b^3,(ab)^4> =", FpGroup(F, [x**2, y**3, (x*y)**4]).order())
print("order <a,c | a^2,c^2,(ac)^3> =", FpGroup(F, [x**2, y**2, (x*y)**3]).order())

def cyc(*prefs):
    def act(w):
        for i, p in enumerate(prefs):
            if w.startswith(p):
                return prefs[(i + 1) % len(prefs)] + w[len(p):]
        return w
    return act
A, B, C = cyc('00', '01'), cyc('01', '10', '11'), cyc('1', '00')

def on_cones(word, cones):  # word: list of maps, applied left to right
    out = []
    for p in cones:
        w = p + '0' * 8
        for f in word:
            w = f(w)
        img = [q for q in cones if w.startswith(q)]
        assert len(img) == 1 and w == img[0] + '0' * 8, "not a rigid cone permutation"
        out.append(img[0])
    return tuple(out)
def closure(gens, cones):
    start = tuple(cones); seen = {start: []}; frontier = [[]]
    while frontier:
        nxt = []
        for wd in frontier:
            for g in gens:
                nw = wd + [g]; key = on_cones(nw, cones)
                if key not in seen:
                    seen[key] = nw; nxt.append(nw)
        frontier = nxt
    return seen
Q, P = ['00', '01', '10', '11'], ['00', '01', '1']
print("|<a,b>| on Q =", len(closure([A, B], Q)), " ab on Q:", dict(zip(Q, on_cones([A, B], Q))))
print("|<a,c>| on P =", len(closure([A, C], P)), " ac on P:", dict(zip(P, on_cones([A, C], P))))

INV = {A: cyc('01', '00'), B: cyc('11', '10', '01'), C: C}
def expand(s):
    L = {'a': A, 'b': B, 'c': C}; i = 0
    def seq():
        nonlocal i
        res = []
        while i < len(s) and s[i] != ')':
            if s[i] == '(':
                i += 1; body = seq(); i += 1
            else:
                body = [L[s[i]]]; i += 1
            inv, rep = False, 1
            if i < len(s) and s[i] == '^':
                i += 1
                if s[i] == '-':
                    inv = True; i += 1
                j = i
                while i < len(s) and s[i].isdigit():
                    i += 1
                rep = int(s[j:i])
            piece = [INV[f] for f in reversed(body)] if inv else body
            res += piece * rep
        return res
    return seq()
RELS = ["a^2", "b^3", "(ab)^4", "c^-1(ac)^2a", "(cab^-1aba)^2cb(cabab^-1a)^2",
        "a(cb)^2a(b^-1c)^2bcabcb^-1cab^-1acb^-1(cb)^2ab^-1",
        "ab^-1cbc(ab^-1)^2cbcb^-1a(b^-1c)^2babcb^-1cab^-1",
        "ca(b^-1c)^2bacabacbc(b^-1ca)^2b(cb^-1)^2(acb)^2cb^-1cab^-1", "c^2", "(ac)^3"]
random.seed(5)
tests = [''.join(random.choice('01') for _ in range(64)) for _ in range(4000)]
ok = True
for r in RELS:
    word = expand(r); bad = 0
    for t in tests:
        w = t
        for f in word:
            w = f(w)
        bad += (w != t)
    ok &= (bad == 0)
    print("relator", r, "length", len(word), "failures", bad)
print("ALL RELATORS FIX RANDOM STRINGS:", ok)
print("CHECKDONE")
