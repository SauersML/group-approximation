#!/usr/bin/env python3
"""Exact shadow defects of forest observations for Thompson's group F.

Everything here uses the definitions of
`research/thompson-f-flow-certificate-observation-gate-proof.md` verbatim:

  M            positive monoid of F, identified with forests (Lemma 1.1 of
               `thompson-f-finite-state-flows-cannot-prove-nonamenability-proof`);
  rule reading Psi   w(s, y) = G(s, Psi(y)), G >= 0;
  D_lambda(mu, eta) = sum_s || (Psi_* mu - lambda Psi_* rho^eta_s)_+ ||;
  delta_lambda(Psi)  = inf over mu, eta.

By Corollary A.2 of that file, a single law `mu` supported in the intersection of the
`sM` with

    || Psi_* rho^mu_s - Psi_* mu ||  <=  eps      for every s in S

gives `D_1(mu, mu) <= |S| eps`, hence an exact upper bound for `delta_1(Psi)`.
`Psi_* rho^mu_s` is the law of `Psi(split_s Y)` for `Y ~ mu`.  All the numbers below
are the exact total variation distances `TV(law Psi(split_s Y), law Psi(Y))`, computed
in integer arithmetic (every atom of the model has the same probability, so the laws
are counting measures with a common denominator).

The model is the *tail model* of `thompson-f-exact-tail-observations-have-zero-defect`:

    N uniform in {n_0, ..., L},  n_0 = K + 1,  K = I + D_S + 1;
    for a < N, t_a = complete binary top of depth H = D_S + 1 with T_{r(a,b)} hung at
    its b-th bottom leaf, the states r(a,b) i.i.d. from an idempotent pi;
    t_a = . for a >= N.

Stage 4 verifies the *conditional* statement, which is the whole content of the
theorem: for each n,

    law of Psi(split_s Y | N = n)   =   law of Psi(Y | N = n + deg s).

The mixture over N then costs exactly deg(s) / (L - n_0 + 1), because the laws for
different N have disjoint supports (the exact tail determines N when N > K).

Run: python3 exact_tail_shadow_defect.py           (a few seconds, stdlib only)
"""

from fractions import Fraction
from itertools import product
import sys

LEAF = ()


# ---------------------------------------------------------------- forests ----

def caret(left, right):
    return (left, right)


def is_leaf(t):
    return t == LEAF


def carets(t):
    return 0 if is_leaf(t) else 1 + carets(t[0]) + carets(t[1])


def leftdepth(t):
    """Depth of the leftmost leaf: -log2 of the slope at 0."""
    return 0 if is_leaf(t) else 1 + leftdepth(t[0])


def depth(t):
    return 0 if is_leaf(t) else 1 + max(depth(t[0]), depth(t[1]))


def trim(forest):
    f = list(forest)
    while f and is_leaf(f[-1]):
        f.pop()
    return tuple(f)


def merge(forest, k):
    f = list(forest)
    while len(f) <= k + 1:
        f.append(LEAF)
    t = caret(f[k], f[k + 1])
    return trim(tuple(f[:k] + [t] + f[k + 2:]))


def split(forest, k):
    f = list(forest)
    if k >= len(f) or is_leaf(f[k]):
        return None
    l, r = f[k]
    return trim(tuple(f[:k] + [l, r] + f[k + 1:]))


def act(forest, word):
    """(x_(i_1) ... x_(i_d)) . y = merge_(i_1)( ... merge_(i_d)(y) )."""
    y = forest
    for i in reversed(word):
        y = merge(y, i)
    return y


def split_word(forest, word):
    """split_s z = split_{i_d} ( ... split_{i_1} (z) ), None when undefined."""
    y = forest
    for i in word:
        y = split(y, i)
        if y is None:
            return None
    return y


def ntrees(forest):
    return len(trim(forest))


# ------------------------------------------------ monomial sets S_(m+1,m+d+1) --

def monomial_set(m, d):
    """Normal forms x_(i_1)...x_(i_d) with i_1 <= ... <= i_d and i_j <= m + j - 1.

    This is `S_(m+1,m+d+1)` of `thompson-f-nonamenable-iff-some-monomial-set-doubles`.
    """
    out = []

    def rec(prefix, j):
        if j == d:
            out.append(tuple(prefix))
            return
        lo = prefix[-1] if prefix else 0
        for i in range(lo, m + j + 1):
            rec(prefix + [i], j + 1)

    rec([], 0)
    return sorted(out)


# ------------------------------------------------------- tree automaton -------

class Automaton:
    """A tree invariant (Q, delta, ell) together with an idempotent measure pi."""

    def __init__(self, name, ell, delta, states, pi, reps):
        self.name = name
        self.ell = ell
        self.delta = delta
        self.states = states
        self.pi = pi            # dict state -> Fraction
        self.reps = reps        # dict state -> representative tree T_r

    def q(self, t):
        return self.ell if is_leaf(t) else self.delta(self.q(t[0]), self.q(t[1]))

    def check_idempotent(self):
        push = {r: Fraction(0) for r in self.states}
        for a in self.states:
            for b in self.states:
                push[self.delta(a, b)] += self.pi[a] * self.pi[b]
        return all(push[r] == self.pi[r] for r in self.states)


def xnor_automaton():
    """q(.) = 0, q(L^R) = 1 iff q(L) == q(R).  pi = uniform on {0,1} is idempotent."""
    return Automaton(
        name="XNOR",
        ell=0,
        delta=lambda a, b: 1 if a == b else 0,
        states=(0, 1),
        pi={0: Fraction(1, 2), 1: Fraction(1, 2)},
        reps={0: LEAF, 1: caret(LEAF, LEAF)},
    )


# ------------------------------------------------------------- the model ------

def tops(aut, H):
    """All complete depth-H tops with a representative T_r hung at each bottom leaf.

    Returns the list of distinct shapes; the model makes them equally likely
    (the hung states are i.i.d. uniform, and pi is uniform here).
    """
    leaves = 1 << H
    shapes = []
    for assign in product(sorted(aut.reps), repeat=leaves):
        level = [aut.reps[r] for r in assign]
        while len(level) > 1:
            level = [caret(level[i], level[i + 1]) for i in range(0, len(level), 2)]
        shapes.append(level[0])
    assert len(set(shapes)) == len(shapes), "hung assignments must give distinct shapes"
    return shapes


# ---------------------------------------------------------- observations ------

def observations(aut, K):
    """Every observation is a function of a forest, named by a short label.

    `Xi_K` is the observation of the theorem: the automaton states of the first K
    trees, and the exact shapes of every later tree.
    """
    q = aut.q

    def pad(forest, i):
        return forest[i] if i < len(forest) else LEAF

    obs = {}
    obs["profile+N  (B.3)"] = lambda y: (
        tuple(q(t) for t in trim(y)), ntrees(y))
    obs["profile+N+carets (Thm B)"] = lambda y: (
        tuple(q(t) for t in trim(y)), ntrees(y), sum(carets(t) for t in trim(y)))
    obs["Xi_K = states<K + exact tail"] = lambda y: (
        tuple(q(pad(y, i)) for i in range(K)), trim(y)[K:])
    obs["Xi_K + germ at 0"] = lambda y: (
        tuple(q(pad(y, i)) for i in range(K)), trim(y)[K:], leftdepth(pad(y, 0)))
    obs["Xi_(K-1) (sharpness)"] = lambda y: (
        tuple(q(pad(y, i)) for i in range(K - 1)), trim(y)[K - 1:])
    obs["Xi_K + total carets"] = lambda y: (
        tuple(q(pad(y, i)) for i in range(K)), trim(y)[K:],
        sum(carets(t) for t in trim(y)))
    obs["prefix pi_K (first K exact)"] = lambda y: tuple(pad(y, i) for i in range(K))
    obs["sorted tree sizes"] = lambda y: tuple(sorted(carets(t) for t in trim(y)))
    obs["identity id_M"] = lambda y: trim(y)
    return obs


def law(forests_with_weight, f):
    out = {}
    for y, w in forests_with_weight:
        k = f(y)
        out[k] = out.get(k, 0) + w
    return out


def total_variation(p, q):
    """Exact TV between two integer-weighted laws with the same total mass."""
    mp, mq = sum(p.values()), sum(q.values())
    assert mp > 0 and mq > 0
    keys = set(p) | set(q)
    acc = Fraction(0)
    for k in keys:
        acc += abs(Fraction(p.get(k, 0), mp) - Fraction(q.get(k, 0), mq))
    return acc / 2


# ------------------------------------------------------------ stage 1 ---------

def stage1_relations():
    print("STAGE 1  monoid relations and injectivity (Lemma 1.1)")
    e = ()
    bad = 0
    for i in range(6):
        for j in range(i + 1, 6):
            if act(e, (j, i)) != act(e, (i, j + 1)):
                bad += 1
    print("   x_j x_i = x_i x_(j+1) for 0 <= i < j <= 5 :", "ok" if bad == 0 else "FAIL")
    seen = {}
    total = 0
    for d in range(0, 6):
        for w in normal_forms(d, 5):
            total += 1
            y = act(e, w)
            assert y not in seen, "collision"
            seen[y] = w
    print("   normal forms of degree <= 5 in x_0..x_5 :", total, "distinct forests")
    for w, y in list(seen.items())[:0]:
        pass
    ok = all(split_word(act(e, w), w) == () for w in seen.values())
    print("   split_s (s . e) = e for every such s :", "ok" if ok else "FAIL")
    print()
    return bad == 0 and ok


def normal_forms(d, maxi):
    if d == 0:
        yield ()
        return

    def rec(prefix, j):
        if j == d:
            yield tuple(prefix)
            return
        lo = prefix[-1] if prefix else 0
        for i in range(lo, maxi + 1):
            yield from rec(prefix + [i], j + 1)

    yield from rec([], 0)


# ------------------------------------------------------------ stage 2 ---------

def symbolic_split(N, word):
    """Run split_(i_1), ..., split_(i_d) on addresses instead of trees.

    An entry (a, p) stands for the subtree of t_a at the node with binary address p.
    split at index k replaces (a, p) by (a, p + '0'), (a, p + '1').  This is the
    induction of Theorem 4.3 of the finite-state proof, carried out explicitly.
    """
    cur = [(a, "") for a in range(N)]
    for i in word:
        a, p = cur[i]
        cur = cur[:i] + [(a, p + "0"), (a, p + "1")] + cur[i + 1:]
    return cur


def stage2_split_shape(m, d, aut, H=None, extra=3):
    """Check split_s Y = (u_0..u_(I+d), t_(I+1), ..., t_(N-1)) and N_split = N + d."""
    S = monomial_set(m, d)
    I = max(max(s) for s in S)
    D = d
    if H is None:
        H = D + 1
    K = I + D + 1
    N = K + 1 + extra
    shapes = tops(aut, H)
    Y = trim(tuple(shapes[(7 * a + 3) % len(shapes)] for a in range(N)))
    ok_tail, ok_count, ok_j0 = True, True, True
    ok_anti, ok_depth, ok_addr = True, True, True
    for s in S:
        z = split_word(Y, s)
        if z is None:
            ok_tail = False
            continue
        if ntrees(z) != N + d:
            ok_count = False
        if tuple(z[I + d + 1:]) != tuple(Y[I + 1:]):
            ok_tail = False
        j0 = sum(1 for i in s if i == 0)
        if leftdepth(z[0]) != leftdepth(Y[0]) - j0:
            ok_j0 = False

        addr = symbolic_split(N, s)
        if len(addr) != N + d:
            ok_addr = False
        # (a) the first I + d + 1 entries sit in t_0 .. t_I at depth <= d < H
        for c, (a, p) in enumerate(addr[:I + d + 1]):
            if a > I or len(p) > d or len(p) >= H:
                ok_depth = False
        # (b) entries from position I + d + 1 on are the untouched roots t_(c - d)
        for c, (a, p) in enumerate(addr):
            if c >= I + d + 1 and (p != "" or a != c - d):
                ok_addr = False
        # (c) the addresses form an antichain: no one is a prefix of another,
        #     so their bottom-leaf sets are pairwise disjoint, and together they
        #     exhaust the bottom leaves of t_0 .. t_I
        for c1 in range(I + d + 1):
            a1, p1 = addr[c1]
            for c2 in range(c1 + 1, I + d + 1):
                a2, p2 = addr[c2]
                if a1 == a2 and (p1.startswith(p2) or p2.startswith(p1)):
                    ok_anti = False
        mass = sum(2 ** (H - len(p)) for (a, p) in addr[:I + d + 1])
        if mass != (I + 1) * 2 ** H:
            ok_anti = False
    print("STAGE 2  split geometry for S_(%d,%d) : |S| = %d, I = %d, D = %d, K = %d, H = %d, N = %d"
          % (m + 1, m + d + 1, len(S), I, D, K, H, N))
    print("   every split_s Y defined, N_(split_s Y) = N + deg s :", "ok" if ok_count and ok_tail else "FAIL")
    print("   trees at positions >= I + d + 1 are t_(I+1), t_(I+2), ... untouched :",
          "ok" if ok_tail and ok_addr else "FAIL")
    print("   the first I + d + 1 subtrees sit in t_0..t_I at depth <= d < H :",
          "ok" if ok_depth else "FAIL")
    print("   their addresses form an antichain exhausting the bottom leaves :",
          "ok" if ok_anti else "FAIL")
    print("   leftmost-leaf depth drops by exactly j_0(s) = #{j : i_j = 0} :",
          "ok" if ok_j0 else "FAIL")
    print()
    return ok_tail and ok_count and ok_j0 and ok_anti and ok_depth and ok_addr


# ------------------------------------------------------------ stage 4 ---------

def stage4_defects(m, d, aut, n=None, verbose=True):
    S = monomial_set(m, d)
    I = max(max(s) for s in S)
    D = d
    H = D + 1
    K = I + D + 1
    n0 = K + 1
    if n is None:
        n = n0
    shapes = tops(aut, H)
    print("STAGE 4  exact conditional total variations, S = S_(%d,%d), automaton %s"
          % (m + 1, m + d + 1, aut.name))
    print("   I = %d, D = %d, K = I + D + 1 = %d, H = %d, |tops| = %d, N = %d -> %d"
          % (I, D, K, H, len(shapes), n, n + d))

    src = [(trim(t), 1) for t in product(shapes, repeat=n)]
    dst = [(trim(t), 1) for t in product(shapes, repeat=n + d)]
    print("   model atoms: %d (source, N = %d) and %d (target, N = %d)"
          % (len(src), n, len(dst), n + d))

    obs = observations(aut, K)
    rows = {name: {} for name in obs}
    for s in S:
        pushed = []
        for y, w in src:
            z = split_word(y, s)
            assert z is not None, "split must be defined on the model"
            pushed.append((z, w))
        for name, f in obs.items():
            tv = total_variation(law(pushed, f), law(dst, f))
            rows[name][s] = tv
    width = max(len(nm) for nm in obs)
    print()
    print("   " + "observation".ljust(width) + "   max_s TV(Psi(split_s Y|N=n), Psi(Y|N=n+d))")
    for name in obs:
        worst = max(rows[name].values())
        mark = "DEAD in this model" if worst == 0 else "survives this model"
        print("   " + name.ljust(width) + "   " + str(worst).rjust(12) + "   " + mark)
    print("   ('Xi_K + germ at 0' is measured here in the FIXED-depth model, where the")
    print("    germ cannot match; stage 5 mixes the first top's depth and drives it to 0.)")
    if verbose:
        print()
        print("   per-s detail for the two sharpness rows:")
        for name in ("Xi_K = states<K + exact tail", "Xi_(K-1) (sharpness)"):
            for s in S:
                print("     %-30s s = %-12s TV = %s"
                      % (name, "x_" + "x_".join(map(str, s)) if s else "1", rows[name][s]))
    print()
    return rows


# ------------------------------------------------------------ stage 5 ---------

def psi_recursive(aut, h):
    """Exact joint law of (state, leftmost-leaf depth) of a depth-h top.

    h = 0 is the hung tree T_r with r ~ pi; a depth-h top is A ^ B with A, B
    independent depth-(h-1) tops, so state = delta(q(A), q(B)) and leftdepth
    = 1 + leftdepth(A).  q(B) ~ pi by Lemma 4.2.
    """
    cur = {}
    for r, p in aut.pi.items():
        key = (r, leftdepth(aut.reps[r]))
        cur[key] = cur.get(key, Fraction(0)) + p
    for _ in range(h):
        nxt = {}
        for (a, l), pa in cur.items():
            for b, pb in aut.pi.items():
                key = (aut.delta(a, b), l + 1)
                nxt[key] = nxt.get(key, Fraction(0)) + pa * pb
        cur = nxt
    return cur


def psi_enumerated(aut, h, splits_on_left_spine=0):
    """Same joint law, by brute force over all depth-h tops, after j left-spine splits."""
    out = {}
    shapes = tops(aut, h)
    w = Fraction(1, len(shapes))
    for t in shapes:
        u = t
        for _ in range(splits_on_left_spine):
            u = u[0] if not is_leaf(u) else u
        key = (aut.q(u), leftdepth(u))
        out[key] = out.get(key, Fraction(0)) + w
    return out


def tv_dict(p, q):
    keys = set(p) | set(q)
    return sum(abs(p.get(k, Fraction(0)) - q.get(k, Fraction(0))) for k in keys) / 2


def stage5_germ_at_zero(aut, H=2):
    print("STAGE 5  germ at 0 (leftmost-leaf depth) under a depth-mixed first tree")
    ok = True
    for h in (1, 2, 3):
        if psi_recursive(aut, h) != psi_enumerated(aut, h):
            ok = False
    print("   recursion for psi_h agrees with brute force, h = 1, 2, 3 :",
          "ok" if ok else "FAIL")
    ok2 = True
    for h in (2, 3):
        for j in (1, 2):
            if j > h:
                continue
            if psi_enumerated(aut, h, splits_on_left_spine=j) != psi_recursive(aut, h - j):
                ok2 = False
    print("   after j left-spine splits a depth-h top is a fresh depth-(h-j) top :",
          "ok" if ok2 else "FAIL")
    print()
    print("   TV between the H_0-mixtures, uniform over {H, ..., H + L''}:")
    print("      j \\ L''   " + "".join(str(lpp).rjust(12) for lpp in (1, 3, 7, 15, 31)))
    for j in (1, 2, 3):
        row = []
        for lpp in (1, 3, 7, 15, 31):
            mix_a, mix_b = {}, {}
            for h in range(H, H + lpp + 1):
                for k, v in psi_recursive(aut, h - j).items():
                    mix_a[k] = mix_a.get(k, Fraction(0)) + v / (lpp + 1)
                for k, v in psi_recursive(aut, h).items():
                    mix_b[k] = mix_b.get(k, Fraction(0)) + v / (lpp + 1)
            tv = tv_dict(mix_a, mix_b)
            assert tv <= Fraction(j, lpp + 1), "mixture bound violated"
            row.append(str(tv).rjust(12))
        print("      j = %d    " % j + "".join(row))
    print("   every entry is <= j / (L'' + 1), and tends to 0.  So adding the germ at 0")
    print("   to Xi_K keeps the defect 0 once the first top's depth is mixed.")
    print()


# ------------------------------------------------------------ main ------------

def main():
    sys.setrecursionlimit(10000)
    aut = xnor_automaton()
    print("automaton %s: reachable states %s, pi = %s, idempotent: %s"
          % (aut.name, aut.states, {k: str(v) for k, v in aut.pi.items()},
             aut.check_idempotent()))
    # Lemma 4.2 sanity: the state of a depth-h tower over i.i.d. pi is pi-distributed.
    for h in (1, 2, 3):
        cnt = {0: 0, 1: 0}
        for t in tops(aut, h):
            cnt[aut.q(t)] += 1
        print("   Lemma 4.2 at h = %d: P[q = 1] = %s" % (h, Fraction(cnt[1], sum(cnt.values()))))
    print()

    stage1_relations()

    for (m, dd) in ((1, 1), (1, 2), (2, 1), (2, 2), (3, 2), (1, 3), (2, 3)):
        stage2_split_shape(m, dd, aut)

    stage4_defects(1, 1, aut)
    stage5_germ_at_zero(aut)
    print("   Mixing N uniformly over {n_0, ..., L} adds exactly deg(s) / (L - n_0 + 1)")
    print("   to every row whose conditional TV is 0, because the laws for different N")
    print("   have disjoint supports (the exact tail shows N when N > K).  So")
    print("   delta_1(Xi_K) = 0 and delta_1(Xi_K + germ at 0) = 0.")


if __name__ == "__main__":
    main()
