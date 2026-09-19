"""Wachter-Weiss check-mark automaton: unencoded C' and binary-encoded C (arXiv:1906.03424v3,
Fig. fig:checkmarkingAutomaton and paragraph 'Encoding over Two Letters'), with continuation id.

Checks for germ-necessity (nekrashevych-fp-iff-cycle-germ-groups-fp, part 1):
  - stability and closedness of the ray family {0^w, 1^w} (C') and {(100)^w, (101)^w} (C, level 3m);
  - the loop arrows [e, y] (states e with e|_y = e) of the germ groupoid;
  - relators used in the hand proof ([A',N], A'NA'^-1 = N, lamp independence, H = <Z,N,K> recursion).
Run:  python3 cm.py
"""
import sys, os, itertools
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'nonc-rn-fp-2026-09-17'))
from autom import Automaton

# ---------------------------------------------------------------- C' over 0,1,g,#,$
LET = ['0', '1', 'g', '#', '$']
SW = (1, 0, 2, 3, 4)
ID = (0, 1, 2, 3, 4)
CP = {  # name: (perm, sections in letter order 0,1,g,#,$)
    'A':  (SW, ('Z', 'Ap', 'e', 'e', 'e')),
    'Ap': (SW, ('N', 'Ap', 'e', 'e', 'e')),
    'Z':  (ID, ('Z', 'N', 'K', 'e', 'e')),
    'N':  (ID, ('N', 'N', 'A', 'e', 'e')),
    'K':  (ID, ('K', 'e', 'K', 'A', 'e')),
}


def eventual(seq_fn, s, y, maxk=64):
    """Iterate s -> s|_y; return (preperiod, period, cycle states)."""
    seen = {}
    k = 0
    while s not in seen:
        seen[s] = k
        s = seq_fn(s, y)
        k += 1
    start = seen[s]
    cyc = [q for q, i in sorted(seen.items(), key=lambda t: t[1]) if i >= start]
    return start, k - start, cyc


def cprime_checks():
    G = Automaton(5, CP)
    out = []
    # signed states: +i, -i ; section at letter x of a single letter
    def sec1(u, x):
        s = G.sec[u][x]
        return s[0] if s else 0
    def outp(u, x):
        return G.perm[u][x]
    letters = [u for i in range(1, 6) for u in (i, -i)]
    fam = {0, 1}
    closed = True
    for y in (0, 1):
        for u in letters:
            pre, per, cyc = eventual(lambda q, yy: sec1(q, yy) if q else 0, u, y)
            e = cyc[0]
            eo = outp(e, y) if e else y
            if per != 1:
                out.append('NOT STABLE %s at %s' % (G.fmt((u,)), LET[y]))
            if eo not in fam:
                closed = False
            out.append('C\': letter %-3s ray %s^w: eventual state %-3s (preperiod %d), eventual output %s'
                       % (G.fmt((u,)), LET[y], G.fmt((e,)) if e else '1', pre, LET[eo]))
    out.append('C\': family {0,1} closed: %s' % closed)
    # loop arrows [e,y]: positive states with e|_y = e
    arrows = [(n, LET[y], LET[G.perm[G.idx[n]][y]]) for n in G.names for y in (0, 1)
              if sec1(G.idx[n], y) == G.idx[n]]
    out.append('C\': arrows [e,y]: y -> e(y): %s' % arrows)
    w = G.word
    tests = {
        "[A',N]": "Ap N Ap' N'",
        "[Z,N]": "Z N Z' N'",
        "A'NA'^-1 N^-1": "Ap N Ap' N'",
        "[K,NKN^-1]": "K N K N' K' N K' N'",
        "[K,N^2KN^-2]": "K N N K N' N' K' N N K' N' N'",
        "[K,AKA^-1]": "K A K A' K' A K' A'",
        "[K,A^3KA^-3]": "K A A A K A' A' A' K' A A A K' A' A' A'",
        "[Z,K] (a relator: Z = K*c, c central)": "Z K Z' K'",
        "[K,N] (not a relator)": "K N K' N'",
    }
    for name, s in tests.items():
        ww = w(s)
        out.append('C\': %-45s trivial=%s  in K_inf=%s' % (name, G.is_trivial(ww), G.in_K_inf(ww)))
    # lamp independence in <A,K>: products of distinct lamp powers nontrivial
    lamps = lambda n: (w("A") * n if n >= 0 else w("A'") * (-n)) + w("K") + (w("A'") * n if n >= 0 else w("A") * (-n))
    bad = 0
    for coeffs in itertools.product((-1, 0, 1), repeat=4):
        if all(c == 0 for c in coeffs):
            continue
        ww = ()
        for n, c in zip(range(4), coeffs):
            if c:
                l = lamps(n)
                ww += l if c > 0 else tuple(-u for u in reversed(l))
        if G.is_trivial(ww):
            bad += 1
    out.append('C\': nontrivial lamp combinations sum c_n A^nKA^-n (n<4, c in -1..1) that are trivial: %d' % bad)
    # H = <Z,N,K> -> <A,K> x Z via (phi, e_Z): sample kernel test
    import random
    random.seed(1)
    agree = 0
    tot = 0
    for _ in range(300):
        L = random.randint(1, 10)
        ww = tuple(random.choice([1, -1]) * random.choice([G.idx['Z'], G.idx['N'], G.idx['K']]) for _ in range(L))
        phi = tuple((1 if u > 0 else -1) * {G.idx['Z']: G.idx['K'], G.idx['N']: G.idx['A'], G.idx['K']: G.idx['K']}[abs(u)] for u in ww)
        eZ = sum((1 if u > 0 else -1) for u in ww if abs(u) == G.idx['Z'])
        a = G.is_trivial(ww)
        b = G.is_trivial(phi) and eZ == 0
        tot += 1
        agree += (a == b)
    out.append("C': w(Z,N,K)=1 iff phi(w)=1 and e_Z(w)=0, random words: %d/%d agree" % (agree, tot))
    return out


# ---------------------------------------------------------------- encoded C over {0,1} (boxed digits)
def encoded(L):
    codes = {'0': '100', '1': '101', '#': '110', '$': '111'}
    gam = ['0' + ''.join(b) for b in itertools.product('01', repeat=L)]
    code_of = dict(codes)
    for gc in gam:
        code_of[gc] = gc
    allcodes = set(code_of.values())
    ppre = {''} | {c[:i] for c in allcodes for i in range(1, len(c))}
    base = {n: (p, dict(zip(LET, s))) for n, (p, s) in CP.items()}
    def cp_out(n, a):  # letter image
        p = base[n][0]
        return LET[p[LET.index(a)]]
    def cp_sec(n, a):
        return base[n][1][a]
    def name(n, x):
        if n == 'e':
            return 'e'
        return n + '_' + (x if x else 'E')
    gens = {}
    for n in base:
        for x in sorted(ppre):
            perm = [0, 0]
            secs = ['e', 'e']
            for b in '01':
                xb = x + b
                bi = int(b)
                if xb in ppre:
                    perm[bi] = bi
                    secs[bi] = name(n, xb)
                else:
                    assert xb in allcodes, xb
                    if xb in (codes['0'], codes['1']):
                        a = '0' if xb == codes['0'] else '1'
                        oa = cp_out(n, a)
                        perm[bi] = int(codes[oa][-1])
                        secs[bi] = name(cp_sec(n, a), '')
                    elif xb in (codes['#'], codes['$']):
                        a = '#' if xb == codes['#'] else '$'
                        perm[bi] = bi
                        secs[bi] = name(cp_sec(n, a), '')
                    else:
                        perm[bi] = bi
                        secs[bi] = name(cp_sec(n, 'g'), '')
            gens[name(n, x)] = (tuple(perm), tuple(secs))
    return Automaton(2, gens)


def encoded_checks(L, m=None):
    G = encoded(L)
    out = []
    y0, y1 = (1, 0, 0), (1, 0, 1)
    def secw(u, v):
        """section of a single signed letter u at binary word v, as signed letter or 0"""
        cur = (u,)
        for x in v:
            if not cur:
                return 0
            _, s = G.act(cur, x)
            cur = G.reduce(s)
        return cur[0] if cur else 0
    def outw(u, v):
        img = []
        cur = (u,)
        for x in v:
            if not cur:
                img.append(x)
                continue
            px, s = G.act(cur, x)
            img.append(px)
            cur = G.reduce(s)
        return tuple(img)
    letters = [u for i in range(1, len(G.names) + 1) for u in (i, -i)]
    # eventual periods along y^k at level 3
    per_lcm = 1
    from math import gcd
    info = {}
    for y in (y0, y1):
        for u in letters:
            pre, per, cyc = eventual(lambda q, yy: secw(q, yy) if q else 0, u, y)
            per_lcm = per_lcm * per // gcd(per_lcm, per)
            info[(u, y)] = (pre, per, cyc)
    if m is None:
        m = per_lcm
    Y0, Y1 = y0 * m, y1 * m
    fam = {Y0, Y1}
    closed = True
    stable = True
    for Y in (Y0, Y1):
        for u in letters:
            pre, per, cyc = eventual(lambda q, yy: secw(q, yy) if q else 0, u, Y)
            if per != 1:
                stable = False
            e = cyc[0]
            eo = outw(e, Y) if e else Y
            if eo not in fam:
                closed = False
    arrows = []
    for n in G.names:
        u = G.idx[n]
        for Y, nm in ((Y0, 'y0'), (Y1, 'y1')):
            if secw(u, Y) == u:
                tgt = outw(u, Y)
                arrows.append((n, nm, 'y0' if tgt == Y0 else ('y1' if tgt == Y1 else str(tgt))))
    out.append('C_enc L=%d (L mod 3 = %d): %d states; lcm of eventual periods at level 3 = %d; at level 3m, m=%d: stable=%s closed=%s'
               % (L, L % 3, len(G.names), per_lcm, m, stable, closed))
    out.append('   loop arrows [e,y] -> e(y): %s' % arrows)
    return G, out, arrows


if __name__ == '__main__':
    for line in cprime_checks():
        print(line)
    for L in (1, 2, 3, 4, 5):
        G, out, arrows = encoded_checks(L)
        for line in out:
            print(line)
    # L = 2: commutation among the germ generators at (100)^w (open case L = 2 mod 3)
    G = encoded(2)
    inv = lambda t: tuple(-u for u in reversed(t))
    gg = {'Z': 'Z_E', 'N': 'N_E', 'K': 'K_E', 'K_00': 'K_00', 'K_01': 'K_01', 'K_0': 'K_0',
          "A'K_01A'^-1": "Ap_E K_01 Ap_E'"}
    nm = list(gg)
    for i, a in enumerate(nm):
        for b in nm[i + 1:]:
            x, y = G.word(gg[a]), G.word(gg[b])
            print('L=2 germ gens: [%s,%s] trivial=%s   %s=%s: %s' % (
                a, b, G.is_trivial(x + y + inv(x) + inv(y)), a, b, G.is_trivial(x + inv(y))))
