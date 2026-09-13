#!/usr/bin/env python3
"""Linton tree test for the length-15 residue family G = <x,y,t | x^t = u, u^t = y>.

For each CLASS line of residue-output.txt (Magnus word a_1^e a_0^* a_2^* a_0^* a_2^* in some cyclic
order), solve the unique level-1 letter: u = a_1 as a word in x = a_0, y = a_2. With H = F(x,y),
A = <x,u>, B = <u,y>, psi(x) = u, psi(u) = y, the test checks:
  T1  A cap B has rank 1, contains u, and is the only core component of rank >= 1 in the A x B pullback;
  T2  the A x A and B x B pullbacks have only the diagonal component (A and B malnormal);
  T3  the only monochromatic cycles are the x-loop at the base of Gamma_A and the y-loop at the base
      of Gamma_B;
  T4  x in A, u in A, u in B, y in B, x not in B, y not in A.
If T1-T4 hold then s_Z(psi) = 2. The graph of cyclic stabilisers then has the single H-edge
[<u>]_A - [<u>]_B, and every t-edge joins one of its ends to [<x>]_A or [<y>]_B, so it has no
cyclically alternating closed path (route row29-virtually-special-via-linton-z-stable-graph).
Output: one VERDICT line per class.
Usage: lintontree.py residue-output.txt
"""
import sys, ast, re
from algext import stallings
from lintonstab import pullback, components, core, reduce, inv

def succ(E, l):
    return {u: v for (u, lab, v) in E if lab == l}

def monocycles(nv, E):
    out = []
    for l in 'xy':
        s, seen = succ(E, l), set()
        for start in range(nv):
            if start in seen or start not in s:
                continue
            path, u = [], start
            while u in s and u not in path:
                path.append(u); u = s[u]
            if u == start:
                out.append((l, len(path), list(path)))
            seen.update(path)
    return out

def member(E, w):
    fwd = {(u, lab): v for (u, lab, v) in E}
    bwd = {(v, lab): u for (u, lab, v) in E}
    u = 0
    for ch in w:
        key = (u, ch.lower())
        nxt = fwd.get(key) if ch.islower() else bwd.get(key)
        if nxt is None:
            return False
        u = nxt
    return u == 0

def word_of(seq):
    letters = {0: ('x', 'X'), 2: ('y', 'Y')}
    idx = [i for i, (h, e) in enumerate(seq) if h == 1]
    if len(idx) != 1 or abs(seq[idx[0]][1]) != 1:
        return None
    i = idx[0]; e = seq[i][1]
    rest = seq[i + 1:] + seq[:i]
    R = ''.join((letters[h][0] if ex > 0 else letters[h][1]) * abs(ex) for h, ex in rest)
    R = reduce(R)
    return reduce(inv(R)) if e == 1 else R

def pb_summary(g1, g2):
    n1, E1 = stallings(g1); n2, E2 = stallings(g2)
    PE = pullback(E1, E2)
    comps = components(PE, extra=[(0, 0)])
    bc = next(c for c in comps if (0, 0) in c)
    BE = {e for e in PE if e[0] in bc and e[2] in bc}
    base_rank = len(BE) - len(bc) + 1
    others = []
    for comp in comps:
        V, E = core(comp, PE)
        if not V:
            continue
        r = len(E) - len(V) + 1
        if r >= 1 and (0, 0) not in comp:
            others.append(r)
    return base_rank, others

def main():
    for line in open(sys.argv[1]):
        if not line.startswith('CLASS '):
            continue
        w = line.split()[1]
        tag = line.split()[-1]
        seq = ast.literal_eval(re.search(r'seq=(\[[^\]]*\])', line).group(1))
        u = word_of(seq)
        if u is None:
            print('VERDICT %s %s SKIP no unique level-1 letter' % (w, tag)); continue
        A, B = ['x', u], [u, 'y']
        rAB, oAB = pb_summary(A, B)
        rAA, oAA = pb_summary(A, A)
        rBB, oBB = pb_summary(B, B)
        nA, EA = stallings(A); nB, EB = stallings(B)
        mA, mB = monocycles(nA, EA), monocycles(nB, EB)
        T1 = rAB == 1 and not oAB and member(EA, u) and member(EB, u)
        T2 = not oAA and not oBB
        T3 = mA == [('x', 1, [0])] and mB == [('y', 1, [0])]
        T4 = member(EA, 'x') and member(EB, 'y') and not member(EB, 'x') and not member(EA, 'y')
        ok = T1 and T2 and T3 and T4
        print('VERDICT %s %s u=%s AxB=(%d,%s) AxA_off=%s BxB_off=%s monoA=%s monoB=%s T1=%s T2=%s T3=%s T4=%s TREE=%s'
              % (w, tag, u, rAB, oAB, oAA, oBB, mA, mB, T1, T2, T3, T4, ok))
    print('SENTINEL_DONE')

if __name__ == '__main__':
    main()
