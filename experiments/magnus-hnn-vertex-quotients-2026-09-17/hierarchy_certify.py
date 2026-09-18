#!/usr/bin/env python3
"""Certify that a torsion-free one-relator group lies in the class H of hereditarily
Hughes-free embeddable groups, by walking a Magnus-Moldavanskii hierarchy.

Every step used is a theorem of the repository:
  free        : <X | w> with a letter occurring once is free.
  freefactor  : letters absent from w give free factors (H closed under free products).
  nielsen     : an automorphism of F(X) (Nielsen move) does not change the group.
  retract-A/C : Magnus HNN B*_theta whose base retracts onto an edge group
                (vertex-injective-quotients-give-hughes-free-division-rings, item 6).
  bs-quotient : Magnus HNN with cyclic edge groups; B -> Z injective on both edge groups,
                so G maps to Z[1/pq] x| Z injectively on edges (edge-injective quotient lemma,
                edge-injective-quotients-give-hughes-free-division-rings, items 1-2).
  root        : w in <other letters, b^k>, k >= 2: G = G_k *_{s = b^k} <b>, certified when G_k is
                and some f: G_k -> Z has f(s) != 0 (item 3, root adjunction).
  root-tower  : two-generator Magnus HNN whose top (or bottom) letter occurs in one cyclic
                syllable and whose other exponent sums are not all zero (item 4).
Mode 'old' allows only free, freefactor, nielsen, retract-A/C; mode 'new' adds the rest.
A word is a tuple of (letter, +-1).  Output 'uncertified' means only that these rules
did not certify the group, not that it lies outside H.
"""
import itertools, sys
from functools import lru_cache


def red(w):
    out = []
    for x in w:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def cred(w):
    w = list(red(w))
    while len(w) >= 2 and w[0][0] == w[-1][0] and w[0][1] == -w[-1][1]:
        w = w[1:-1]
    return tuple(w)


def inv(w):
    return tuple((a, -e) for a, e in reversed(w))


def exps(w):
    d = {}
    for a, e in w:
        d[a] = d.get(a, 0) + e
    return d


def is_proper_power(w):
    n = len(w)
    for k in range(2, n + 1):
        if n % k == 0 and w == w[: n // k] * k:
            return True
    return False


def subst(w, sigma):
    out = []
    for a, e in w:
        img = sigma.get(a, ((a, 1),))
        out.extend(img if e == 1 else inv(img))
    return red(out)


def canon(w):
    """Canonical relabelling (letters renamed by first occurrence) up to rotation."""
    best = None
    n = len(w)
    for ww in (w, inv(w)):
        for r in range(n):
            rot = ww[r:] + ww[:r]
            names, lab = {}, []
            for a, e in rot:
                if a not in names:
                    names[a] = len(names)
                lab.append((names[a], e))
            lab = tuple(lab)
            if best is None or lab < best:
                best = lab
    return best


def short_words(letters, maxlen):
    ws = [()]
    frontier = [()]
    gens = [(a, e) for a in letters for e in (1, -1)]
    for _ in range(maxlen):
        nf = []
        for w in frontier:
            for g in gens:
                if w and w[-1][0] == g[0] and w[-1][1] == -g[1]:
                    continue
                nf.append(w + (g,))
        ws.extend(nf)
        frontier = nf
    return ws


def find_retraction(r, kill, keep, maxlen=2, cap=40000):
    """Look for sigma: kill-letters -> words in keep-letters with sigma(r) = 1 in F(keep).
    Includes the exact 'solve' move for a kill-letter occurring once.  Returns sigma or None."""
    kill = sorted(kill)
    cands = short_words(sorted(keep), maxlen)
    occ = {a: sum(1 for b, _ in r if b == a) for a in kill}
    # solve move: one kill-letter occurring once, others from cands
    for s in kill:
        if occ[s] != 1:
            continue
        others = [a for a in kill if a != s]
        if len(cands) ** len(others) > cap:
            continue
        for choice in itertools.product(cands, repeat=len(others)):
            sigma = dict(zip(others, choice))
            i = next(j for j, (b, _) in enumerate(r) if b == s)
            e = r[i][1]
            rest = subst(r[i + 1:] + r[:i], sigma)  # r ~ s^e * rest
            img = inv(rest) if e == 1 else rest
            sigma[s] = img
            if not subst(r, sigma):
                return sigma
    if len(cands) ** len(kill) > cap:
        return None
    for choice in itertools.product(cands, repeat=len(kill)):
        sigma = dict(zip(kill, choice))
        if not subst(r, sigma):
            return sigma
    return None


def nielsen_zero(w):
    """Apply Nielsen moves until some letter has exponent sum 0.  Returns new word."""
    for _ in range(60):
        e = exps(w)
        if len(e) < 2 or any(v == 0 for v in e.values()):
            return w
        ls = sorted(e, key=lambda a: abs(e[a]))
        y, x = ls[0], ls[1]  # |e[y]| <= |e[x]|
        k = -round(e[x] / e[y])  # y -> y x^k changes exp(x) to e[x] + k e[y]
        sigma = {y: ((y, 1),) + ((x, 1 if k > 0 else -1),) * abs(k)}
        w = cred(subst(w, sigma))
    return w


def rewrite(w, t):
    p, out = 0, []
    for a, e in w:
        if a == t:
            p += e
        else:
            out.append(((a, p), e))
    return tuple(out)


def bs_quotient_ok(r, a0, a1):
    """Cyclic edges <a0>, <a1>: is there f in Hom(B,Z) = e^perp with f(a0) f(a1) != 0?"""
    e = exps(r)
    letters = sorted(e)
    others = [x for x in letters if e[x] != 0]
    # e^perp is contained in {f(a0)=0} iff e is a multiple of the a0 coordinate vector
    only_a0 = all(x == a0 for x in others)
    only_a1 = all(x == a1 for x in others)
    if not others:
        return True  # e = 0, any f
    return not only_a0 and not only_a1


def syllables(w):
    out = []
    for a, e in w:
        if out and out[-1][0] == a:
            out[-1][1] += e
        else:
            out.append([a, e])
    if len(out) > 1 and out[0][0] == out[-1][0]:
        out[0][1] += out[-1][1]
        out.pop()
    return out


def root_rule(w, mode, depth, memo):
    """w in <other letters, b^k>, k >= 2: G = G_k *_{s=b^k} <b>.  Certified when G_k is
    and some f: G -> Z is nonzero on b (edge-injective quotient lemma)."""
    e = exps(w)
    for b in sorted(e):
        syl = [x for x in syllables(w) if x[0] == b]
        k = 0
        for _, n in syl:
            k = __import__("math").gcd(k, abs(n))
        if k < 2:
            continue
        others = [x for x in e if x != b]
        if not (any(e[x] != 0 for x in others) or e[b] == 0):
            continue
        s = ("root", b)
        wk = []
        for a, n in syllables(w):
            if a == b:
                wk.extend([(s, 1 if n > 0 else -1)] * (abs(n) // k))
            else:
                wk.extend([(a, 1 if n > 0 else -1)] * abs(n))
        ok, why = certify(tuple(wk), mode, depth + 1, memo)
        if ok:
            return True, "root%d[%s]" % (k, why)
    return None


def root_tower_ok(r, lv):
    """Two-generator Magnus HNN (one letter family).  Root-tower theorem: if the top letter
    occurs in r' in one cyclic syllable and the other letters' exponent sums are not all
    zero (or the same with top and bottom swapped), then G lies in H."""
    if len(lv) != 1:
        return False
    (g, (lo, hi)), = lv.items()
    if hi == lo:
        return False
    e = exps(r)
    syl = syllables(r)
    ntop = sum(1 for a, _ in syl if a == (g, hi))
    nbot = sum(1 for a, _ in syl if a == (g, lo))
    rest_top = any(e.get((g, p), 0) != 0 for p in range(lo, hi))
    rest_bot = any(e.get((g, p), 0) != 0 for p in range(lo + 1, hi + 1))
    return (ntop == 1 and rest_top) or (nbot == 1 and rest_bot)

def certify(w, mode, depth=0, memo=None):
    """Return (ok, reason) for G = <letters of w | w>; letters not in w are free factors."""
    if memo is None:
        memo = {}
    w = cred(w)
    if not w:
        return True, "free"
    key = canon(w)
    if key in memo:
        return memo[key]
    w = key
    if is_proper_power(w):
        res = (False, "torsion")
        memo[key] = res
        return res
    if depth > 40:
        return False, "depth"
    memo[key] = (False, "cycle")
    occ = {}
    for a, _ in w:
        occ[a] = occ.get(a, 0) + 1
    if len(occ) == 1 or min(occ.values()) == 1:
        res = (True, "free")
        memo[key] = res
        return res
    if mode == "new":
        rr = root_rule(w, mode, depth, memo)
        if rr is not None:
            memo[key] = rr
            return rr
    e = exps(w)
    zeros = [a for a in e if e[a] == 0]
    if not zeros:
        ok, why = certify(nielsen_zero(w), mode, depth + 1, memo)
        res = (ok, "nielsen(" + why + ")")
        memo[key] = res
        return res
    best = (False, "open")
    for t in zeros:
        r = rewrite(w, t)
        lv = {}
        for (g, p), _ in r:
            lo, hi = lv.get(g, (p, p))
            lv[g] = (min(lo, p), max(hi, p))
        top = {(g, hi) for g, (lo, hi) in lv.items() if hi > lo}
        bot = {(g, lo) for g, (lo, hi) in lv.items() if hi > lo}
        letters = {a for a, _ in r}
        rank = sum(hi - lo for lo, hi in lv.values())
        if mode == "new" and root_tower_ok(r, lv):
            memo[key] = (True, "root-tower")
            return memo[key]
        okB, whyB = certify(r, mode, depth + 1, memo)
        if not okB:
            if best[1] == "open":
                best = (False, "base:" + whyB)
            continue
        if rank == 0:
            return_ = (True, "freeprod")
        else:
            Aset = {(g, p) for (g, p) in letters if p < lv[g][1]} | {
                (g, p) for g, (lo, hi) in lv.items() for p in range(lo, hi)}
            Cset = {(g, p) for g, (lo, hi) in lv.items() for p in range(lo + 1, hi + 1)}
            killA = {x for x in letters if x not in Aset}
            killC = {x for x in letters if x not in Cset}
            return_ = None
            if find_retraction(r, killA, Aset) is not None:
                return_ = (True, "retract-A[" + whyB + "]")
            elif find_retraction(r, killC, Cset) is not None:
                return_ = (True, "retract-C[" + whyB + "]")
            elif mode == "new" and rank == 1:
                (g, (lo, hi)), = [(g, v) for g, v in lv.items() if v[1] > v[0]]
                if bs_quotient_ok(r, (g, lo), (g, hi)):
                    return_ = (True, "bs-quotient[" + whyB + "]")
        if return_ is not None:
            memo[key] = return_
            return return_
        best = (False, "open-rank%d" % rank)
    memo[key] = best
    return best


def parse(s):
    """'a b A B' style: lowercase letter = generator, uppercase = inverse, optional ^n."""
    w = []
    for tok in s.split():
        base, _, pw = tok.partition("^")
        n = int(pw) if pw else 1
        a = base.lower()
        e = 1 if base.islower() else -1
        if n < 0:
            e, n = -e, -n
        w.extend([(a, e)] * n)
    return red(w)
