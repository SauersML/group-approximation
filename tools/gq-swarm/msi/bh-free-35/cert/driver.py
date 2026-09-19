#!/usr/bin/env python3
"""bh-free-35: bounded-range noncommutative certificate search for local tiling algebras at scale D = 1.

Window algebra A_W: idempotents e_a(z), z in W, with
  (Q1) orthogonal partitions of unity at each site,
  (Q2) commutation at l1-distance <= 2,
  (Q3) vanishing of every pattern on a subset of some ball B_1(z) that is not in the language
       (an illegal domino or triangle, or a locally legal pattern that does not extend to the 5x5 box around z).
All relations hold in the infinite local tiling algebra U_1, so if [e_a(0), e_b(v)] reduces to 0 modulo a two-sided
Groebner basis of A_W truncated at degree DEG (Singular letterplace), the commutator vanishes in U_1: a sound
certificate. 'NO' means undecided at that window and degree, not a refutation.
Python 3.6 compatible.  Usage: driver.py OUTDIR
"""
import itertools, os, signal, subprocess, sys, time

OUTDIR = sys.argv[1]
os.makedirs(OUTDIR, exist_ok=True)
T0 = time.time()
DEADLINE = 530.0
SUMMARY = open(os.path.join(OUTDIR, 'summary.txt'), 'a')


def log(s):
    line = '[%6.1fs] %s' % (time.time() - T0, s)
    print(line, flush=True)
    SUMMARY.write(line + '\n')
    SUMMARY.flush()


def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def l1(z): return abs(z[0]) + abs(z[1])


E1, E2 = (1, 0), (0, 1)
PLUS = [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]


class SFT:
    def __init__(self, name, n, hok, vok, tri=None):
        self.name, self.n, self.hok, self.vok, self.tri = name, n, hok, vok, tri

    def locally_legal(self, assign):
        for z, a in assign.items():
            w = add(z, E1)
            if w in assign and not self.hok(a, assign[w]):
                return False
            w = add(z, E2)
            if w in assign and not self.vok(a, assign[w]):
                return False
            if self.tri is not None:
                u, w = add(z, E1), add(z, E2)
                if u in assign and w in assign and not self.tri(a, assign[u], assign[w]):
                    return False
        return True

    def extendable(self, assign, center):
        """Is there a locally legal assignment of the 5x5 box around center extending assign?"""
        cells = [(center[0] + i, center[1] + j) for j in range(-2, 3) for i in range(-2, 3)]
        cur = {}

        def ok(c, a):
            l, b = add(c, (-1, 0)), add(c, (0, -1))
            if l in cur and not self.hok(cur[l], a):
                return False
            if b in cur and not self.vok(cur[b], a):
                return False
            if self.tri is not None:
                z, u = add(c, (0, -1)), add(c, (1, -1))  # c is the top vertex z+e2 of triangle at z
                if z in cur and u in cur and not self.tri(cur[z], cur[u], a):
                    return False
            return True

        def rec(k):
            if k == len(cells):
                return True
            c = cells[k]
            dom = [assign[c]] if c in assign else range(self.n)
            for a in dom:
                if ok(c, a):
                    cur[c] = a
                    if rec(k + 1):
                        return True
                    del cur[c]
            return False
        return rec(0)


def legal_patterns(sft, T):
    """All locally legal assignments on the site list T (backtracking)."""
    out, cur = [], {}

    def rec(k):
        if k == len(T):
            out.append(dict(cur))
            return
        for a in range(sft.n):
            cur[T[k]] = a
            if sft.locally_legal(cur):
                rec(k + 1)
            del cur[T[k]]
    rec(0)
    return out


def var(i, a): return 'x%d_%d' % (i, a)


def relations(sft, W, use_ext=True):
    idx = {z: i for i, z in enumerate(W)}
    n, rels = sft.n, []
    for z in W:
        i = idx[z]
        rels.append(' + '.join(var(i, a) for a in range(n)) + ' - 1')
        for a in range(n):
            rels.append('%s*%s - %s' % (var(i, a), var(i, a), var(i, a)))
            for b in range(n):
                if a != b:
                    rels.append('%s*%s' % (var(i, a), var(i, b)))
    for z, w in itertools.combinations(W, 2):
        if l1(sub(z, w)) <= 2:
            i, j = idx[z], idx[w]
            for a in range(n):
                for b in range(n):
                    rels.append('%s*%s - %s*%s' % (var(i, a), var(j, b), var(j, b), var(i, a)))
    nq3 = 0
    for z in W:  # illegal dominoes and triangles
        for e, okf in ((E1, sft.hok), (E2, sft.vok)):
            w = add(z, e)
            if w in idx:
                for a in range(n):
                    for b in range(n):
                        if not okf(a, b):
                            rels.append('%s*%s' % (var(idx[z], a), var(idx[w], b))); nq3 += 1
        if sft.tri is not None and add(z, E1) in idx and add(z, E2) in idx:
            u, w = add(z, E1), add(z, E2)
            for a, b, c in itertools.product(range(n), repeat=3):
                if not sft.tri(a, b, c):
                    rels.append('%s*%s*%s' % (var(idx[z], a), var(idx[u], b), var(idx[w], c))); nq3 += 1
    seen = set() if use_ext else None  # locally legal but non-extendable patterns on dominoes and on B_1(z) cap W
    for z in (W if use_ext else []):
        S = sorted(add(z, h) for h in PLUS if add(z, h) in idx)
        subsets = [tuple(sorted((u, add(u, e)))) for u in S for e in (E1, E2) if add(u, e) in S]
        if len(S) >= 3:
            subsets.append(tuple(S))
        for T in subsets:
            if T in seen:
                continue
            seen.add(T)
            for pat in legal_patterns(sft, list(T)):
                if not sft.extendable(pat, z):
                    rels.append('*'.join(var(idx[u], pat[u]) for u in T)); nq3 += 1
    return rels, nq3


def window(v, detour):
    lo0, hi0 = min(0, v[0]) - 2, max(0, v[0]) + 2
    lo1, hi1 = min(0, v[1]) - 2, max(0, v[1]) + 2
    return [(i, j) for i in range(lo0, hi0 + 1) for j in range(lo1, hi1 + 1)
            if l1((i, j)) + l1(sub(v, (i, j))) <= l1(v) + detour]


SING = None


def run_singular(path, tmax):
    global SING
    cands = [['sage', '-singular', '-q', path], ['sage', '-sh', '-c', 'Singular -q %s' % path]]
    order = [SING] if SING is not None else range(len(cands))
    for k in order:
        p = subprocess.Popen(cands[k], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            out, _ = p.communicate(timeout=tmax)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL); p.communicate()
            return None, 'TIMEOUT'
        out = out.decode('utf-8', 'replace')
        if 'PROBE' in out or 'GB ' in out or SING is not None:
            SING = k
            return out, 'ok'
    return out, 'FAILED'


def script(W, rels, targets, deg, char=0):
    names = [var(i, a) for i in range(len(W)) for a in range(NCUR)]
    s = ['LIB "freegb.lib";', 'ring r = %d,(%s),dp;' % (char, ','.join(names)),
         'def R = freeAlgebra(r, %d);' % deg, 'setring R;', 'option(redSB); option(redTail);', 'ideal I;']
    for k in range(0, len(rels), 150):
        s.append('I = I, ' + ', '.join(rels[k:k + 150]) + ';')
    s.append('ideal G = twostd(I);')
    s.append('print("GB " + string(size(G)));')
    for k, (p, q) in enumerate(targets):
        s.append('if (reduce(%s*%s - %s*%s, G) == 0) { print("T %d OK"); } else { print("T %d NO"); }'
                 % (p, q, q, p, k, k))
    s.append('quit;')
    return '\n'.join(s) + '\n'


NCUR = 0


def case(sft, vs, detour, deg, tmax, label, use_ext=True):
    global NCUR
    NCUR = sft.n
    for v in vs:
        if time.time() - T0 > DEADLINE - tmax:
            log('%s v=%s SKIPPED (budget)' % (label, v)); continue
        W = window(v, detour)
        idx = {z: i for i, z in enumerate(W)}
        rels, nq3 = relations(sft, W, use_ext)
        pairs = [(a, b) for a in range(sft.n) for b in range(sft.n)]
        targets = [(var(idx[(0, 0)], a), var(idx[v], b)) for a, b in pairs]
        path = os.path.join(OUTDIR, '%s_%d_%d.sing' % (label, v[0], v[1]))
        open(path, 'w').write(script(W, rels, targets, deg))
        t1 = time.time()
        out, st = run_singular(path, tmax)
        dt = time.time() - t1
        if out is not None:
            open(path + '.out', 'w').write(out)
        oks = out.count(' OK') if out else 0
        nos = out.count(' NO') if out else 0
        gb = [l for l in (out or '').splitlines() if l.startswith('GB ')]
        fails = [pairs[int(l.split()[1])] for l in (out or '').splitlines() if l.startswith('T ') and l.endswith('NO')]
        log('%s v=%s |W|=%d vars=%d rels=%d q3=%d deg=%d %s %.1fs %s  certified %d/%d  undecided %d%s'
            % (label, v, len(W), len(W) * sft.n, len(rels), nq3, deg, st, dt, gb[0] if gb else 'GB ?',
               oks, len(pairs), nos, ('  undecided pairs %s' % fails[:12]) if fails else ''))


# ---- SFTs ------------------------------------------------------------------------------------------
TRUE2 = lambda a, b: True
led = SFT('ledrappier', 2, TRUE2, TRUE2, tri=lambda a, b, c: (a + b + c) % 2 == 0)
# planted rigid with local coordinates: letter 2k+val, k in Z/2 increments to the right, constant upward
ledk = SFT('ledrappier-x-coords', 4, lambda a, b: b // 2 == (a // 2 + 1) % 2, lambda a, b: b // 2 == a // 2,
           tri=lambda a, b, c: ((a % 2) + (b % 2) + (c % 2)) % 2 == 0)
full = SFT('full-shift', 2, TRUE2, TRUE2)
colp = SFT('colour-product', 4, lambda a, b: a // 2 == b // 2, lambda a, b: a % 2 == b % 2)
tilesU = ['FOJO', 'FOHL', 'JMFP', 'DMFK', 'HPJP', 'HPHN', 'HKFP', 'HKDP', 'BOIO', 'GLEO', 'GLCL', 'ALIO',
          'EPGP', 'EPIP', 'IPGK', 'IPIK', 'IKBM', 'IKAK', 'CNIP']  # Labbe's Omega_U, convention RTLB
RT = [t[0] for t in tilesU]; TP = [t[1] for t in tilesU]; LF = [t[2] for t in tilesU]; BT = [t[3] for t in tilesU]
labbe = SFT('labbe-omega-u', 19, lambda a, b: RT[a] == LF[b], lambda a, b: TP[a] == BT[b])


def main():
    probe = os.path.join(OUTDIR, 'probe.sing')
    open(probe, 'w').write('LIB "freegb.lib";\nring r = 0,(x,y),dp;\ndef R = freeAlgebra(r, 4);\nsetring R;\n'
                           'ideal I = x*x - x, y*y - y, x*y*x - x*y;\nideal G = twostd(I);\n'
                           'print("PROBE " + string(size(G)));\n'
                           'if (reduce(x*y*x - x*y, G) == 0) { print("P1 OK"); } else { print("P1 NO"); }\n'
                           'if (reduce(x*y - y*x, G) == 0) { print("P2 OK"); } else { print("P2 NO"); }\nquit;\n')
    out, st = run_singular(probe, 90)
    log('probe %s singular-cmd=%s :: %s' % (st, SING, ' | '.join((out or '').split('\n')[-6:])))
    if SING is None:
        log('ABORT: no working Singular'); return
    # run 2: finish the planted calibration on rectangle windows; Labbe local algebra (dominoes only) at degree 3
    case(ledk, [(2, 1), (1, 2), (2, -1), (1, -2)], 0, 4, 60, 'ledk2')
    case(ledk, [(0, 3)], 2, 4, 60, 'ledk2v')
    case(labbe, [(2, 1), (1, 2)], 0, 3, 170, 'labbe3', use_ext=False)
    log('done')


main()
