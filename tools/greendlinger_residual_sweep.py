#!/usr/bin/env python3
"""Bounded adversary search for the two residuals of the free-group Greendlinger gate.

READ THIS FIRST
===============

This program refutes-or-supports two open predicates of the router's
small-cancellation lane by brute force over small relator families.  Every
predicate below is transcribed from Lean; the Lean file and line are quoted at
each transcription site, and the transcription is meant to be *literal*,
including the places where the Lean statement quantifies more widely than its
own callers do.  Where a literal reading was impossible or ambiguous, the choice
is recorded under MODELLING DECISIONS.

    mode A   GroupApproximation/Sofic/GreendlingerDeepThreeFactor.lean:261
             `DeepOverrunDepth R` -- the n=3 three-factor overrun count.

    mode B   GroupApproximation/Sofic/GreendlingerSharpTwins.lean:1083
             `LandingProductionBetaSharp R lam`, attacked through the
             falsification handle `ne_nil_of_landingProductionBetaSharp`
             (GroupApproximation/Sofic/GreendlingerLandingProd.lean:627), plus
             the per-factor leaf `StoppingAlternativeBetaSharp`
             (GreendlingerLandingProd.lean:219) and the overhang census of that
             file's section 9.

Both modes enumerate over an alphabet of `--alphabet` generators (default 2, the
router's own `Fin 2`), letters encoded as bytes: generator `g` with Bool `b`
becomes the byte `2*g + b`, so formal inversion is `x ^ 1` and a word is a
`bytes` object.  `FreeGroup.invRev` is `bytes(x ^ 1 for x in reversed(w))`.

CLI
---

    python3 tools/greendlinger_residual_sweep.py --mode both \\
        --alphabet 2 --max-relator-length 2 --max-relators 2 \\
        --max-conjugator-length 3 --workers 16 --out results/sweep

    --mode {A,B,both,selftest,verify}
    --alphabet N              generators (default 2); letters = 2N
    --min-relator-length L    (default 1)
    --max-relator-length L    (default 2)
    --max-relators K          relator-set size, 1..K (default 1)
    --max-conjugator-length C  bound on |c| in every enumerated factor (default 2)
    --minimality-cap M        bound on |c'| in the *shorter-expression* search
                              (default 3); see SOUNDNESS below
    --lams 1/6,1/7,1/8        constants to report the metric condition against
    --workers N               processes (default: cpu_count)
    --out PREFIX              writes PREFIX.tsv and PREFIX.witnesses.json
    --limit-relator-sets N    stop after N families (default: no limit)
    --limit-reps N            pool size for multi-relator families (default 40)
    --shard i --num-shards n  split the relator enumeration across jobs
    --time-budget SECONDS     per-family wall clock cap; rows are flagged
    --verify-json PATH        with --mode verify: re-check recorded witnesses
                              at the *current* --minimality-cap

WHAT EACH MODE TESTS
--------------------

mode A, per family R and per triple of factors:
  enumerate heads `(c,t)` and tails `(c2,t2),(c3,t3)` with every `t` in
  `symmetrization R` and every palindrome `c ++ t ++ invRev c` reduced; form the
  tail word `W2 = (conjEval [(mk c2,t2),(mk c3,t3)]).toWord`; take every `M`
  that is simultaneously a suffix of `palindrome c t` and satisfies
  `W2 = invRev M ++ B'` (these are exactly the suffixes of length at most the
  free-cancellation length between the head palindrome and `W2`, and they are
  nested, which is what makes the enumeration a single interval); keep those
  with `|c| < |M|` and with the overrun `not (invRev M <+: palindrome c2 t2)`;
  solve `B' = (palindrome c3 t3).drop N` for `N`; and for EVERY `j` with
  `6j < |t|` and `|c| + |t| < |M| + j` evaluate

      2 * ((N - |c3|) + (|M| + j - (|c| + |t|))) < |t3|          (truncated sub)

  Failures are candidate refutations.  Each is then (i) put through the
  `IsMinimalConjExpr` check, and (ii) searched for a Greendlinger arc anyway --
  `GreendlingerAt R d B'` at `d = |M| + j - (|c| + |t|)` -- so the report
  distinguishes "the inequality is false but the conclusion still holds" from
  "the conclusion is false".

mode B, per family R:
  B0  the structural witness for `StoppingAlternativeBetaSharp` at a one-factor
      landing expression (`f = []`);
  B1  the substantive search: two-factor instances with `B' = []`, which by
      `ne_nil_of_landingProductionBetaSharp` refute
      `LandingProductionBetaSharp R lam` for every lam <= 1/6 at which the
      family is still C'(lam);
  B2  the overhang census of GreendlingerLandingProd section 9: two-factor
      (beta)-regime instances with nonempty overhang `q`, recording
      `|q| + |E|` against `lam * |t'|` for each lam, together with
      `StoppingAlternativeBetaSharp` refutations at a nonempty tail.

SOUNDNESS, AND THE ONE CAP THAT MATTERS
---------------------------------------

`IsMinimalConjExpr R e g` (GreendlingerWeight.lean:234) is
`ConjValid R e` and `conjEval e = g` and `e.length` least over ALL valid
expressions for `g` and, among that length, `conjWeight e = sum of norms of the
conjugators` least.  Three of the four clauses are checked exactly here:

  * length 0 is `g = 1`;
  * length 1 is exact and cap-free.  By `exists_palindrome_factor` every
    one-factor value is `c' ++ t' ++ invRev c'` with `t'` symmetrized, and by
    `norm_conjugator_le` the palindromic conjugator is no longer than any `x`
    realizing the same conjugate; so scanning the splits of the reduced word of
    `g` decides both existence and least weight;
  * least weight AT THE SAME LENGTH is exact, because a weight budget `W`
    bounds each conjugator by `W`, and `exists_palindromic_isMinimalConjExpr`
    says the palindromic normal form never weighs more than what it replaces.

The remaining clause -- "no expression of length `k` for `1 < k < |e|` exists,
at any weight" -- is genuinely unbounded and is where `--minimality-cap` goes.
A family is reported as minimal only "up to cap M", and every witness record
carries the cap it was established at.  This matters in one direction only:
a too-small cap can make a NON-minimal expression look minimal, which would
produce a spurious refutation.  Re-run any witness with `--mode verify
--verify-json ... --minimality-cap <larger>` before anyone acts on it.

Before the expensive check runs, four cheap NECESSARY conditions from
GreendlingerWeight.lean are applied to adjacent factor pairs -- `not_absorb`,
`not_absorb_inv`, `overhang_le` (slide) and `overhang_le_meet`.  Each is a
theorem "a minimal expression cannot look like this", so a violation is a sound
rejection, and rejections here are free.

MODELLING DECISIONS
-------------------

1.  `IsPiece` (SmallCancellationRouter.lean:141) is a common PREFIX of two
    DISTINCT elements of the symmetrization, not a common subword; rotations
    are in the symmetrization, so prefixes already reach every position.  The
    metric condition is checked against the whole symmetrization, and the
    binding instance for a given piece is the SHORTEST symmetrized word it
    prefixes.  The empty piece is a piece as soon as two symmetrized words
    exist, and it costs nothing because relators are nonempty.

2.  `M` in mode A is a free variable constrained by two equations, not "the"
    leading cancellation block.  Every admissible `M` is tested.  They form the
    interval of suffixes up to the cancellation length, which is proved inline
    (`admissible_blocks`).

3.  `N` in mode A is likewise universally quantified in the Lean predicate.
    When `B'` is nonempty it is pinned to `|palindrome c3 t3| - |B'|`.  When
    `B'` is EMPTY every `N` at or beyond `|palindrome c3 t3|` satisfies the
    hypothesis and the conclusion fails for large `N` outright.  Those are
    reported separately, tagged `unbounded_N`, because they refute the
    predicate as written for a reason that is arithmetic rather than
    geometric -- the intended `N` is the bounded one that
    `exists_three_factor_landing_drop` produces.  They are never mixed into the
    `inequality` count.

4.  `StoppingAlternativeBetaSharp`'s first four arguments `c E M e` occur in
    exactly one hypothesis, `not ConjugatorAbsorbedSite c E M e`.  At `e = []`
    that hypothesis is vacuously TRUE, because a list equal to an append ending
    in a cons cannot be nil.  The sweep therefore reports B0 witnesses at
    `e = []`, which is the literal reading.  If the leaf is restated with `b`
    tied to the head block, point `--mode B` at the restated predicate: the
    census B2 already computes `|q| + |E|` at the adjacent factor, which is
    that predicate's left disjunct at `b = |M|`.

5.  `FreeGroup.IsCyclicallyReduced` is taken to mean "every rotation is
    reduced", equivalently reduced with `last != inverse of first`.

6.  WHICH FAMILIES EXIST, and it is not what one expects.  The Lean predicates
    quantify over every `R` that is cyclically reduced and C'(1/6); nothing
    asks the relators to be primitive.  Over `Fin 2` the aperiodic one-relator
    families are indeed scarce -- if all `2|r|` symmetrized words are distinct
    they need pairwise distinct prefixes of length `L+1` with
    `L = ceil(|r|/6) - 1`, and there are only `4 * 3^L` reduced words of that
    length, which rules out every `|r|` in 3..12 -- but a PROPER POWER
    `r = u^k` has only `2|u|` symmetrized words however long it is, and those
    families are C'(1/6) at every length.  `{a^k}` has a symmetrization of size
    2, `{(ab)^k}` and `{(abb)^k}` of size 4, `{(aabb)^k}` of size 8.  So the
    cheap, fast, genuinely admissible corner of the search space is the
    periodic one, and the sweep enumerates it first because the symmetrization
    is tiny and every factor loop is short.  A refutation there is a refutation
    of the predicate as stated.  The aperiodic families start at `|r| = 13`
    over `Fin 2` and at `|r| = 7` over `Fin 3`.

Python 3.9+, standard library only.
"""

from __future__ import annotations

import argparse
import itertools
import json
import multiprocessing as mp
import os
import sys
import time
from fractions import Fraction

# ---------------------------------------------------------------------------
# 1.  Word primitives.  A word is `bytes`; a letter is `2*generator + bool`.
# ---------------------------------------------------------------------------


def invrev(w: bytes) -> bytes:
    """FreeGroup.invRev: reverse, flipping the Bool of every letter."""
    return bytes(x ^ 1 for x in reversed(w))


def is_reduced(w: bytes) -> bool:
    """FreeGroup.IsReduced: no adjacent cancelling pair."""
    for i in range(len(w) - 1):
        if w[i] ^ 1 == w[i + 1]:
            return False
    return True


def is_cyclically_reduced(w: bytes) -> bool:
    """Every rotation reduced: reduced, and the wrap-around does not cancel."""
    if not is_reduced(w):
        return False
    return len(w) < 2 or w[-1] ^ 1 != w[0]


def free_reduce(w: bytes) -> bytes:
    out = bytearray()
    for x in w:
        if out and out[-1] ^ 1 == x:
            out.pop()
        else:
            out.append(x)
    return bytes(out)


def cancel_len(u: bytes, v: bytes) -> int:
    """How many letters die when the reduced words `u` and `v` are multiplied."""
    i = 0
    nu = len(u)
    n = nu if nu < len(v) else len(v)
    while i < n and u[nu - 1 - i] ^ 1 == v[i]:
        i += 1
    return i


def mul(u: bytes, v: bytes) -> bytes:
    """Reduced word of the product of two reduced words."""
    i = cancel_len(u, v)
    return u[: len(u) - i] + v[i:]


def rotate(w: bytes, n: int) -> bytes:
    """List.rotate: drop (n % len) ++ take (n % len)."""
    if not w:
        return w
    k = n % len(w)
    return w[k:] + w[:k]


def palindrome(c: bytes, t: bytes) -> bytes:
    """GreendlingerNormalForm.palindrome: c ++ t ++ invRev c."""
    return c + t + invrev(c)


def reduced_words(maxlen: int, nletters: int) -> list:
    """All reduced words of length <= maxlen, deterministic order."""
    out = [b""]
    frontier = [b""]
    for _ in range(maxlen):
        nxt = []
        for w in frontier:
            last = w[-1] if w else None
            for x in range(nletters):
                if last is not None and x == last ^ 1:
                    continue
                nxt.append(w + bytes([x]))
        out.extend(nxt)
        frontier = nxt
    return out


def cyclically_reduced_words(length: int, nletters: int):
    """All cyclically reduced words of exactly `length`, deterministic order."""
    if length == 0:
        return
    for w in reduced_words(length, nletters):
        if len(w) == length and is_cyclically_reduced(w):
            yield w


# ---------------------------------------------------------------------------
# 2.  Symmetrization, pieces, and the metric condition.
# ---------------------------------------------------------------------------


def symmetrization(relators) -> list:
    """SmallCancellationRouter.symmetrization: all rotations of every relator
    and of every formal inverse.  Returned sorted, so the sweep is deterministic."""
    S = set()
    for r in relators:
        if not r:
            continue
        ir = invrev(r)
        for n in range(len(r)):
            S.add(rotate(r, n))
            S.add(rotate(ir, n))
    return sorted(S)


def metric_small_cancellation(S, lam: Fraction) -> bool:
    """MetricSmallCancellation, checked exactly.

    A piece is a common prefix of two distinct symmetrized words; the condition
    is `|p| < lam * |w|` for every symmetrized `w` that `p` prefixes, so the
    binding `w` is the shortest one, and it suffices to walk the prefix lengths.
    """
    if not S:
        return True
    num, den = lam.numerator, lam.denominator
    maxlen = max(len(w) for w in S)
    for k in range(maxlen + 1):
        groups = {}
        for w in S:
            if len(w) >= k:
                g = groups.get(w[:k])
                if g is None:
                    groups[w[:k]] = [len(w), 1]
                else:
                    g[1] += 1
                    if len(w) < g[0]:
                        g[0] = len(w)
        for _p, (minlen, count) in groups.items():
            if count >= 2 and not (k * den < num * minlen):
                return False
    return True


def largest_lam(S, lams) -> Fraction:
    """The smallest lam in `lams` at which the family is still C'(lam), or None.

    C'(lam) is monotone: it gets harder as lam shrinks, so this reports how
    sharp the family is."""
    best = None
    for lam in sorted(lams):
        if metric_small_cancellation(S, lam):
            best = lam
            break
    return best


def prefix_minlen_index(S) -> dict:
    """prefix -> length of the shortest symmetrized word carrying it."""
    d = {}
    for s in S:
        for k in range(len(s) + 1):
            p = s[:k]
            cur = d.get(p)
            if cur is None or len(s) < cur:
                d[p] = len(s)
    return d


# ---------------------------------------------------------------------------
# 3.  The located conclusion.
# ---------------------------------------------------------------------------


def greendlinger_at(pmin: dict, n: int, w: bytes):
    """GreendlingerThreeFactor.GreendlingerAt R n w, decided.

    `w = A ++ u ++ C` with `n <= |A|` and some symmetrized `s` with `u <+: s`
    and `|s| < 2|u|`.  `pmin[u]` is the shortest `s` carrying `u` as a prefix,
    so the existential over `s` is one dictionary lookup."""
    L = len(w)
    for a in range(n, L):
        for b in range(a + 1, L + 1):
            u = w[a:b]
            m = pmin.get(u)
            if m is None:
                break  # no symmetrized word carries this prefix; nor any longer u
            if m < 2 * (b - a):
                return {"start": a, "u": u.hex(), "min_relator_len": m}
    return None


# ---------------------------------------------------------------------------
# 4.  Expressions, and minimality.
# ---------------------------------------------------------------------------


def conj_eval(expr) -> bytes:
    """GreendlingerWeight.conjEval, as a reduced word.

    `expr` is a list of `(c, s)` with `c` a conjugator word and `s` a relator
    word; the value is the product of `mk c * mk s * (mk c)^{-1}`."""
    g = b""
    for c, s in expr:
        cr = free_reduce(c)
        sr = free_reduce(s)
        g = mul(g, mul(mul(cr, sr), invrev(cr)))
    return g


def conj_weight(expr) -> int:
    """GreendlingerWeight.conjWeight: the total conjugator norm."""
    return sum(len(free_reduce(c)) for c, _ in expr)


def min_weight_one_factor(g: bytes, sset: frozenset):
    """Least conjugator norm over ONE-factor expressions for `g`; None if none.

    Exact and cap-free: by `exists_palindrome_factor` a one-factor value is
    `c' ++ t' ++ invRev c'` with `t'` symmetrized, and by `norm_conjugator_le`
    no realizing element is shorter than that `c'`."""
    n = len(g)
    for k in range(n // 2 + 1):
        u = g[:k]
        if g[n - k:] == invrev(u) and g[k: n - k] in sset:
            return k
    return None


def build_atoms(S, cap: int, nletters: int):
    """Every palindromic factor with conjugator length <= cap, sorted by weight.

    These are the building blocks of the bounded minimality search: by
    `exists_palindromic_isMinimalConjExpr` any expression may be replaced,
    factor by factor, by a palindromic one of no greater weight."""
    atoms = []
    for c in reduced_words(cap, nletters):
        for t in S:
            p = palindrome(c, t)
            if is_reduced(p):
                atoms.append((len(c), p))
    atoms.sort(key=lambda wv: (wv[0], wv[1]))
    return atoms


def min_weight_expr(g: bytes, k: int, atoms, budget: int, sset: frozenset,
                    memo: dict):
    """Least total weight over length-`k` expressions for `g` with weight < budget.

    Returns None if there is none inside the budget and the atom set.  Atoms are
    sorted by weight, so the loop can stop as soon as the first factor alone
    exhausts the budget."""
    if budget <= 0:
        return None
    if k == 0:
        return 0 if not g else None
    if k == 1:
        r = min_weight_one_factor(g, sset)
        return r if (r is not None and r < budget) else None
    key = (g, k, budget)
    hit = memo.get(key, 0)
    if hit != 0:
        return None if hit is None else hit
    best = None
    for w, v in atoms:
        if w >= budget:
            break
        rest = mul(invrev(v), g)
        r = min_weight_expr(rest, k - 1, atoms, budget - w, sset, memo)
        if r is not None and (best is None or w + r < best):
            best = w + r
            if best == 0:
                break
    memo[key] = best
    return best


def weight_lemma_violation(expr):
    """The four cheap necessary conditions of GreendlingerWeight.lean.

    Each lemma says a minimal expression cannot look like this, so a hit is a
    sound rejection.  `expr` must already be in palindromic normal form."""
    for i in range(len(expr) - 1):
        c, t = expr[i]
        c2, t2 = expr[i + 1]
        # not_absorb_of_minimal: c = c' ++ (t' ++ q'') with c' = c2, t' = t2.
        if t2 and c.startswith(c2 + t2) and is_reduced(c):
            return "not_absorb"
        # not_absorb_inv_of_minimal: c2 = c ++ (invRev t ++ Z).
        if t and c2.startswith(c + invrev(t)) and is_reduced(c2):
            return "not_absorb_inv"
        # overhang_le_of_minimal: c = c2 ++ q, t2 = q ++ p, t = invRev p' ++ invRev p,
        # and then |q| <= 2|p| is forced.
        if c.startswith(c2) and is_reduced(c):
            q = c[len(c2):]
            if t2.startswith(q):
                p = t2[len(q):]
                if t.endswith(invrev(p)) and len(q) > 2 * len(p):
                    return "overhang_le"
        # overhang_le_of_minimal_meet: c2 = c ++ y, t = invRev v ++ invRev y,
        # t2 = v ++ u, and then |y| <= |v| is forced.
        if c2.startswith(c) and is_reduced(c2):
            y = c2[len(c):]
            if t.endswith(invrev(y)):
                v = invrev(t[: len(t) - len(y)])
                if t2.startswith(v) and len(y) > len(v):
                    return "overhang_le_meet"
    return None


def _pair_min_weight(atoms, state, eff_cap):
    """value -> least `|c1| + |c2|` over ordered pairs of atoms spelling it.

    Built once per family and cap; it turns the same-length check at three
    factors from a quadratic scan per call into one dictionary lookup per
    leading atom, which is what makes the sweep affordable."""
    key = ("pairs", eff_cap)
    d = state.get(key)
    if d is None:
        d = {}
        for w1, v1 in atoms:
            for w2, v2 in atoms:
                v = mul(v1, v2)
                w = w1 + w2
                cur = d.get(v)
                if cur is None or w < cur:
                    d[v] = w
        state[key] = d
    return d


def is_minimal_conj_expr(expr, S, sset, cap: int, nletters: int, state: dict):
    """IsMinimalConjExpr, decided up to `cap` on the shorter-expression clause.

    Returns (verdict, reason, cap_used).  `verdict` is True only when every
    clause passed; `reason` names the clause that failed otherwise.  `state` is
    a per-family scratch dict: it carries the atom sets, the search memo and the
    per-expression verdicts, all of which are safe to share because they depend
    only on the family and the cap."""
    n = len(expr)
    W = conj_weight(expr)
    eff_cap = max(cap, W)
    vkey = ("verdict", eff_cap, tuple(expr))
    hit = state.get(vkey)
    if hit is not None:
        return hit
    viol = weight_lemma_violation(expr)
    if viol is not None:
        state[vkey] = (False, viol, eff_cap)
        return state[vkey]
    g = conj_eval(expr)
    atoms = state.get(("atoms", eff_cap))
    if atoms is None:
        atoms = build_atoms(S, eff_cap, nletters)
        state[("atoms", eff_cap)] = atoms
    memo = state.setdefault(("memo", eff_cap), {})

    def done(verdict, reason):
        state[vkey] = (verdict, reason, eff_cap)
        return state[vkey]

    # (a) no strictly shorter expression, with every conjugator up to the cap.
    for k in range(n):
        if k == 0:
            if not g:
                return done(False, "length_0")
            continue
        if k == 1:
            if min_weight_one_factor(g, sset) is not None:
                return done(False, "length_1")
            continue
        if min_weight_expr(g, k, atoms, k * eff_cap + 1, sset, memo) is not None:
            return done(False, "length_%d" % k)
    # (b) no lighter expression of the same length.  Exact rather than capped:
    # a total weight below `W` bounds every conjugator by `W <= eff_cap`, so the
    # atom set already contains every competitor.
    if W > 0:
        if n == 3:
            pairs = _pair_min_weight(atoms, state, eff_cap)
            for w1, v1 in atoms:
                if w1 >= W:
                    break
                rest = pairs.get(mul(invrev(v1), g))
                if rest is not None and w1 + rest < W:
                    return done(False, "lighter_same_length")
        elif min_weight_expr(g, n, atoms, W, sset, memo) is not None:
            return done(False, "lighter_same_length")
    return done(True, None)


# ---------------------------------------------------------------------------
# 5.  ConjugatorAbsorbedSite.
# ---------------------------------------------------------------------------


def conjugator_absorbed_site(c: bytes, E: bytes, M: bytes, e):
    """GreendlingerAlphaPlumb.ConjugatorAbsorbedSite c E M e, decided.

    `e` is a list of palindromic factors `(c_i, t_i)`.  Every existential is
    pinned rather than searched:

      * the split `e = e1 ++ ((mk c', t') :: f)` ranges over the |e| cut points;
      * `c'` is forced to the reduced representative of the stored conjugator,
        because `IsReduced (palindrome c' t')` forces `c'` reduced;
      * `d` is forced likewise -- `c = d ++ q` with `c` reduced makes `d`
        reduced, and `mk d` is given;
      * `A` is forced by the decomposition equation;
      * `N` runs over `0 .. |W_f|`, which covers every case: beyond `|W_f|` the
        drop is empty, `A` is the whole word, and both inequalities only
        tighten with `N`.
    """
    W = conj_eval(e)
    for k in range(len(e)):
        e1 = e[:k]
        ck, tk = e[k]
        f = e[k + 1:]
        cprime = free_reduce(ck)
        tprime = tk
        if not is_reduced(palindrome(cprime, tprime)):
            continue
        d = mul(conj_eval(e1), cprime)
        if not c.startswith(d):
            continue
        q = c[len(d):]
        if not tprime.startswith(q):
            continue
        if not rotate(tprime, len(q)).startswith(invrev(E)):
            continue
        Wf = conj_eval([(cprime, tprime)] + f)
        for N in range(len(Wf) + 1):
            tail = Wf[N:]
            if not W.endswith(tail):
                continue
            A = W[: len(W) - len(tail)]
            if N <= len(cprime) + len(E) and \
               len(M) + N <= len(A) + len(cprime) + len(E):
                return {"split": k, "c_prime": cprime.hex(), "q": q.hex(),
                        "N": N, "A_len": len(A)}
    return None


# ---------------------------------------------------------------------------
# 6.  Factor enumeration, and the block interval.
# ---------------------------------------------------------------------------


def build_factors(S, cmax: int, nletters: int):
    """All `(c, t, palindrome c t)` with `t` symmetrized and the palindrome reduced."""
    out = []
    for c in reduced_words(cmax, nletters):
        for t in S:
            p = palindrome(c, t)
            if is_reduced(p):
                out.append((c, t, p))
    return out


def admissible_blocks(P1: bytes, W2: bytes) -> int:
    """The largest `m` with `P1` ending in `M`, `|M| = m`, and `W2 = invRev M ++ B'`.

    `W2[:m] == invRev(P1[-m:])` says exactly that `W2[j] == P1[-1-j] ^ 1` for
    every `j < m`, which is the free-cancellation count between the two reduced
    words.  So the admissible blocks are nested and form the interval `0..m0`."""
    return cancel_len(P1, W2)


# ---------------------------------------------------------------------------
# 7.  Mode A: the three-factor overrun count.
# ---------------------------------------------------------------------------


def mode_a(relators, cfg, deadline):
    S = symmetrization(relators)
    sset = frozenset(S)
    pmin = prefix_minlen_index(S)
    nletters = 2 * cfg["alphabet"]
    facs = build_factors(S, cfg["cmax"], nletters)
    stats = {k: 0 for k in ("configs", "overrun_configs", "no_valid_N",
                            "j_instances", "ineq_fail", "unbounded_N",
                            "unbounded_N_minimal", "minimal_refutations",
                            "arc_present", "truncated")}
    witnesses = []
    atom_cache = {}
    reasons = {}

    npairs = len(facs) * len(facs)
    if npairs > cfg["max_tail_pairs"]:
        stats["truncated"] = 1
        return stats, witnesses, "too_many_tail_pairs:%d" % npairs

    # Tail pairs, indexed by their word so the head can look up the long prefix
    # its own overrun requires.
    tails = []
    for i2, (c2, t2, P2) in enumerate(facs):
        for i3, (c3, t3, P3) in enumerate(facs):
            tails.append((mul(P2, P3), i2, i3))
    tails.sort(key=lambda x: x[0])
    keys = [x[0] for x in tails]

    import bisect

    for c, t, P1 in facs:
        if time.perf_counter() > deadline:
            stats["truncated"] = 1
            break
        jmax = (len(t) - 1) // 6 if t else -1
        if jmax < 0:
            continue
        # A j exists only if |M| + j > |c| + |t| for some j <= jmax.
        m_min = max(len(c) + 1, len(c) + len(t) + 1 - jmax)
        if m_min > len(P1):
            continue
        need = invrev(P1[len(P1) - m_min:])
        lo = bisect.bisect_left(keys, need)
        idx = lo
        while idx < len(keys) and keys[idx].startswith(need):
            W2, i2, i3 = tails[idx]
            idx += 1
            c2, t2, P2 = facs[i2]
            c3, t3, P3 = facs[i3]
            m0 = admissible_blocks(P1, W2)
            for m in range(m_min, m0 + 1):
                M = P1[len(P1) - m:]
                Bp = W2[m:]
                stats["configs"] += 1
                if P2.startswith(invrev(M)):
                    continue  # not an overrun: the block stays inside factor 2
                stats["overrun_configs"] += 1
                jlo = max(0, len(c) + len(t) - m + 1)
                if jlo > jmax:
                    continue  # no admissible offset: not an instance at all
                if not Bp:
                    # Every N >= |palindrome c3 t3| satisfies the hypothesis
                    # `B' = (palindrome c3 t3).drop N`, and the conclusion fails
                    # for large N outright.  Tagged separately; see header note 3.
                    stats["unbounded_N"] += 1
                    expr = [(c, t), (c2, t2), (c3, t3)]
                    ok, reason, cap_used = is_minimal_conj_expr(
                        expr, S, sset, cfg["min_cap"], nletters, atom_cache)
                    if not ok:
                        reasons[reason] = reasons.get(reason, 0) + 1
                        continue
                    stats["unbounded_N_minimal"] += 1
                    if len(witnesses) < cfg["max_witnesses"]:
                        witnesses.append(_witness_a(
                            relators, c, t, c2, t2, c3, t3, M, Bp, None, jlo,
                            "unbounded_N", None, cap_used))
                    continue
                if len(Bp) > len(P3) or not P3.endswith(Bp):
                    # exists_three_factor_landing_drop says this cannot happen
                    # under the stated hypotheses; a nonzero count here is a
                    # transcription bug on this side, not a mathematical finding.
                    stats["no_valid_N"] += 1
                    continue
                N = len(P3) - len(Bp)
                intrusion = N - len(c3) if N > len(c3) else 0
                for j in range(jlo, jmax + 1):
                    stats["j_instances"] += 1
                    d = m + j - (len(c) + len(t))
                    if 2 * (intrusion + d) < len(t3):
                        continue
                    stats["ineq_fail"] += 1
                    expr = [(c, t), (c2, t2), (c3, t3)]
                    ok, reason, cap_used = is_minimal_conj_expr(
                        expr, S, sset, cfg["min_cap"], nletters, atom_cache)
                    if not ok:
                        reasons[reason] = reasons.get(reason, 0) + 1
                        continue
                    stats["minimal_refutations"] += 1
                    arc = greendlinger_at(pmin, d, Bp)
                    if arc is not None:
                        stats["arc_present"] += 1
                    if len(witnesses) < cfg["max_witnesses"]:
                        witnesses.append(_witness_a(
                            relators, c, t, c2, t2, c3, t3, M, Bp, N, j,
                            "inequality", arc, cap_used))
    return stats, witnesses, _fmt_reasons(reasons)


def _fmt_reasons(reasons):
    """Why candidates died on minimality -- the difference between a range that
    is too small (everything collapses to one factor) and a genuine absence."""
    return ";".join("%s=%d" % kv for kv in sorted(reasons.items()))


def _witness_a(relators, c, t, c2, t2, c3, t3, M, Bp, N, j, kind, arc, cap):
    return {
        "mode": "A",
        "target": "DeepOverrunDepth",
        "kind": kind,
        "relators": [r.hex() for r in relators],
        "c": c.hex(), "t": t.hex(),
        "c2": c2.hex(), "t2": t2.hex(),
        "c3": c3.hex(), "t3": t3.hex(),
        "M": M.hex(), "B_prime": Bp.hex(),
        "N": N, "j": j,
        "lhs_note": "2*((N-|c3|)+(|M|+j-(|c|+|t|))) < |t3|",
        "arc": arc,
        "minimality_cap": cap,
    }


# ---------------------------------------------------------------------------
# 8.  Mode B: the landing residual, the leaf, and the overhang census.
# ---------------------------------------------------------------------------


def mode_b(relators, cfg, deadline):
    S = symmetrization(relators)
    sset = frozenset(S)
    nletters = 2 * cfg["alphabet"]
    facs = build_factors(S, cfg["cmax"], nletters)
    lams = cfg["lams"]
    stats = {k: 0 for k in ("b0_structural", "b1_candidates", "b1_site_killed",
                            "b1_refutations", "b2_configs", "b2_site_killed",
                            "b2_beta_instances", "b2_nonempty_overhang",
                            "b2_gap_instances", "b2_leaf_refutations",
                            "b3_site_killed", "b3_gap_instances",
                            "b3_leaf_refutations", "truncated")}
    witnesses = []
    atom_cache = {}
    reasons = {}

    # ---- B0: the one-factor-tail witness for StoppingAlternativeBetaSharp.
    # e = [] makes `not ConjugatorAbsorbedSite c E M e` vacuously true; f = []
    # makes the right disjunct false; b = |P''| makes the left disjunct false.
    for c_p, t_p, P_p in facs:
        ok, _reason, cap_used = is_minimal_conj_expr(
            [(c_p, t_p)], S, sset, cfg["min_cap"], nletters, atom_cache)
        if not ok:
            continue
        b = len(P_p)                      # P'' = palindrome c' t', B'' = []
        if not (len(c_p) < b):
            continue
        left_fails = all((b - len(c_p)) * lam.denominator >=
                         lam.numerator * len(t_p) for lam in lams)
        if not left_fails:
            continue
        stats["b0_structural"] += 1
        if len(witnesses) < cfg["max_witnesses"]:
            witnesses.append({
                "mode": "B0",
                "target": "StoppingAlternativeBetaSharp",
                "kind": "one_factor_tail",
                "relators": [r.hex() for r in relators],
                "c_prime": c_p.hex(), "t_prime": t_p.hex(),
                "f": [], "e": [], "b": b,
                "P_pp_len": len(P_p), "B_pp_len": 0,
                "note": "e=[] voids the site hypothesis; f=[] voids the right "
                        "disjunct; b=|P''| voids the left one",
                "minimality_cap": cap_used,
            })
        break  # one witness per family is the whole content

    # ---- B1 and B2 both walk two-factor instances (head, one-factor tail).
    import bisect

    # Heads indexed by reversed palindrome, so `P1 endswith M` is a prefix query.
    heads = sorted(((bytes(reversed(P1)), c, t, P1) for c, t, P1 in facs),
                   key=lambda x: x[0])
    hkeys = [h[0] for h in heads]

    for c2, t2, P2 in facs:
        if time.perf_counter() > deadline:
            stats["truncated"] = 1
            break

        # ---- B1: B' = [] forces invRev M = P2, i.e. M = invRev P2.
        M = invrev(P2)
        needle = bytes(reversed(M))
        lo = bisect.bisect_left(hkeys, needle)
        idx = lo
        while idx < len(hkeys) and hkeys[idx].startswith(needle):
            _rev, c, t, P1 = heads[idx]
            idx += 1
            if not (len(c) < len(M) <= len(c) + len(t)):
                continue
            E = P1[len(P1) - len(M): len(P1) - len(c)]
            if M != E + invrev(c) or invrev(M) != c + invrev(E):
                continue                      # orientation package
            if not t.endswith(E) or not E:    # E <:+ t, 0 < |E|
                continue
            stats["b1_candidates"] += 1
            if conjugator_absorbed_site(c, E, M, [(c2, t2)]) is not None:
                stats["b1_site_killed"] += 1  # the (alpha) branch owns it
                continue
            expr = [(c, t), (c2, t2)]
            ok, reason, cap_used = is_minimal_conj_expr(
                expr, S, sset, cfg["min_cap"], nletters, atom_cache)
            if not ok:
                reasons["b1:" + str(reason)] = \
                    reasons.get("b1:" + str(reason), 0) + 1
                continue
            stats["b1_refutations"] += 1
            if len(witnesses) < cfg["max_witnesses"]:
                witnesses.append({
                    "mode": "B1",
                    "target": "LandingProductionBetaSharp",
                    "kind": "B_prime_empty",
                    "relators": [r.hex() for r in relators],
                    "c": c.hex(), "t": t.hex(),
                    "c2": c2.hex(), "t2": t2.hex(),
                    "M": M.hex(), "E": E.hex(), "B_prime": "",
                    "j": 0,
                    "lams_refuted": [str(l) for l in lams
                                     if metric_small_cancellation(S, l)],
                    "note": "ne_nil_of_landingProductionBetaSharp forces B' != []",
                    "minimality_cap": cap_used,
                })

        # ---- B2: the (beta) census at the adjacent factor, and leaf refutations.
        for c, t, P1 in facs:
            m0 = admissible_blocks(P1, P2)
            for m in range(len(c) + 1, m0 + 1):
                if m > len(c) + len(t):
                    break                      # hhigh at j = 0
                M2 = P1[len(P1) - m:]
                Bp = P2[m:]
                E = P1[len(P1) - m: len(P1) - len(c)]
                if M2 != E + invrev(c) or not E or not t.endswith(E):
                    continue
                stats["b2_configs"] += 1
                if conjugator_absorbed_site(c, E, M2, [(c2, t2)]) is not None:
                    stats["b2_site_killed"] += 1
                    continue
                stats["b2_beta_instances"] += 1
                if not c.startswith(c2):
                    continue                   # no overhang to speak of
                q = c[len(c2):]
                if not q:
                    continue
                stats["b2_nonempty_overhang"] += 1
                intrusion = len(q) + len(E)     # = |M| - |c'| at the adjacent factor
                gap_lams = [str(l) for l in lams
                            if intrusion * l.denominator >= l.numerator * len(t2)]
                if not gap_lams:
                    continue
                stats["b2_gap_instances"] += 1
                # StoppingAlternativeBetaSharp at b = |M|: the right disjunct
                # needs |P''| <= b with a nonempty continuation; here f = [] so
                # it is false, and the left disjunct is what `gap_lams` records.
                expr = [(c, t), (c2, t2)]
                ok, reason, cap_used = is_minimal_conj_expr(
                    expr, S, sset, cfg["min_cap"], nletters, atom_cache)
                if not ok:
                    reasons["b2:" + str(reason)] = \
                        reasons.get("b2:" + str(reason), 0) + 1
                    continue
                stats["b2_leaf_refutations"] += 1
                if len(witnesses) < cfg["max_witnesses"]:
                    witnesses.append({
                        "mode": "B2",
                        "target": "StoppingAlternativeBetaSharp",
                        "kind": "overhang_gap",
                        "relators": [r.hex() for r in relators],
                        "c": c.hex(), "t": t.hex(),
                        "c2": c2.hex(), "t2": t2.hex(),
                        "M": M2.hex(), "E": E.hex(), "q": q.hex(),
                        "B_prime": Bp.hex(),
                        "b": m, "intrusion": intrusion,
                        "lams_with_gap": gap_lams,
                        "f_len": 0,
                        "minimality_cap": cap_used,
                    })

    # ---- B3: the same question with a SPECTATOR factor available.
    # B2 refutes the leaf only at `f = []`, which section 8 of
    # GreendlingerLandingProd already knows about.  The live question is whether
    # the leaf still fails when the walk has somewhere to hand the block on, so
    # this repeats the test at a two-factor tail, where the right disjunct
    # `|P''| <= b and f != []` is genuinely available.  The spectator's own
    # conjugator is capped separately (default 0) because it only has to exist.
    if cfg["b3"]:
        spectators = [(c3, t3, palindrome(c3, t3))
                      for c3 in reduced_words(cfg["b3_cmax"], nletters)
                      for t3 in S if is_reduced(palindrome(c3, t3))]
        for c2, t2, P2 in facs:
            if time.perf_counter() > deadline:
                stats["truncated"] = 1
                break
            for c3, t3, P3 in spectators:
                W2 = mul(P2, P3)
                mpp = cancel_len(P2, P3)          # what factor 2 loses to f
                Ppp = P2[: len(P2) - mpp]
                Bpp = P3[mpp:]
                # Which block lengths could possibly refute?  All three
                # conditions on `b` are independent of the head, so the range is
                # computed once and an empty one skips the head lookup entirely.
                bmin = None
                for lam in lams:
                    need = -((-lam.numerator * len(t2)) // lam.denominator)
                    cand = max(len(c2) + 1, len(c2) + need)
                    bmin = cand if bmin is None else min(bmin, cand)
                if bmin is None:
                    continue
                bhi = min(len(Ppp) - 1, len(W2))
                for b in range(bmin, bhi + 1):
                    gap = [str(l) for l in lams
                           if (b - len(c2)) * l.denominator >=
                           l.numerator * len(t2)]
                    if not gap:
                        continue
                    # The head must end with `invRev (W2.take b)`; that is a
                    # suffix query, answered by the same reversed index B1 uses.
                    M2 = invrev(W2[:b])
                    needle = bytes(reversed(M2))
                    lo = bisect.bisect_left(hkeys, needle)
                    k = lo
                    while k < len(hkeys) and hkeys[k].startswith(needle):
                        _rev, c, t, P1 = heads[k]
                        k += 1
                        if not (len(c) < b <= len(c) + len(t)):
                            continue
                        E = P1[len(P1) - b: len(P1) - len(c)]
                        if M2 != E + invrev(c) or not E or not t.endswith(E):
                            continue
                        expr = [(c, t), (c2, t2), (c3, t3)]
                        if conjugator_absorbed_site(
                                c, E, M2, [(c2, t2), (c3, t3)]) is not None:
                            stats["b3_site_killed"] += 1
                            continue
                        stats["b3_gap_instances"] += 1
                        ok, reason, cap_used = is_minimal_conj_expr(
                            expr, S, sset, cfg["min_cap"], nletters, atom_cache)
                        if not ok:
                            reasons["b3:" + str(reason)] = \
                                reasons.get("b3:" + str(reason), 0) + 1
                            continue
                        stats["b3_leaf_refutations"] += 1
                        if len(witnesses) < cfg["max_witnesses"]:
                            witnesses.append({
                                "mode": "B3",
                                "target": "StoppingAlternativeBetaSharp",
                                "kind": "overhang_gap_with_spectator",
                                "relators": [r.hex() for r in relators],
                                "c": c.hex(), "t": t.hex(),
                                "c2": c2.hex(), "t2": t2.hex(),
                                "c3": c3.hex(), "t3": t3.hex(),
                                "M": M2.hex(), "E": E.hex(),
                                "P_pp_len": len(Ppp), "B_pp_len": len(Bpp),
                                "b": b, "intrusion": b - len(c2),
                                "lams_with_gap": gap, "f_len": 1,
                                "minimality_cap": cap_used,
                            })
    return stats, witnesses, _fmt_reasons(reasons)


# ---------------------------------------------------------------------------
# 9.  Relator-family enumeration.
# ---------------------------------------------------------------------------


def canonical_reps(minlen, maxlen, nletters, shard, num_shards):
    """One representative per symmetrization class, deterministic order.

    A class is `{rotations of r} union {rotations of invRev r}`; the
    representative is its lexicographic minimum.  The cheap rejection `r is not
    minimal among its own rotations` kills most words before `invRev` is ever
    formed."""
    reps = []
    counter = 0
    for L in range(max(1, minlen), maxlen + 1):
        for w in cyclically_reduced_words(L, nletters):
            counter += 1
            if num_shards > 1 and counter % num_shards != shard:
                continue
            best = w
            bad = False
            for n in range(1, L):
                r = rotate(w, n)
                if r < best:
                    bad = True
                    break
            if bad:
                continue
            iw = invrev(w)
            for n in range(L):
                r = rotate(iw, n)
                if r < best:
                    bad = True
                    break
            if bad:
                continue
            reps.append(w)
    return reps


def relator_families(cfg):
    """Deterministic list of C'(lam)-satisfying families, largest lam first."""
    reps = canonical_reps(cfg["minlen"], cfg["maxlen"], 2 * cfg["alphabet"],
                          cfg["shard"], cfg["num_shards"])
    pool = reps[: cfg["limit_reps"]] if cfg["max_relators"] > 1 else reps
    out = []
    seen = 0
    for size in range(1, cfg["max_relators"] + 1):
        source = reps if size == 1 else pool
        for combo in itertools.combinations(source, size):
            if not all(is_cyclically_reduced(r) and r for r in combo):
                continue
            S = symmetrization(combo)
            lam = largest_lam(S, cfg["lams"])
            if lam is None:
                continue
            out.append((list(combo), str(lam), len(S)))
            seen += 1
            if cfg["limit_families"] and seen >= cfg["limit_families"]:
                return out
    return out


# ---------------------------------------------------------------------------
# 10.  Driver.
# ---------------------------------------------------------------------------


def run_family(args):
    idx, relators, lam_str, ssize, cfg = args
    deadline = time.perf_counter() + cfg["time_budget"]
    t0 = time.perf_counter()
    rows = []
    witnesses = []
    for mode in cfg["modes"]:
        fn = mode_a if mode == "A" else mode_b
        stats, wit, note = fn(relators, cfg, deadline)
        rows.append({
            "idx": idx, "mode": mode,
            "relators": ",".join(r.hex() for r in relators),
            "sym_size": ssize, "sharpest_lam": lam_str,
            "note": note, "elapsed": round(time.perf_counter() - t0, 3),
            **stats,
        })
        witnesses.extend(wit)
    return rows, witnesses


A_COLUMNS = ["idx", "mode", "relators", "sym_size", "sharpest_lam", "configs",
             "overrun_configs", "no_valid_N", "j_instances", "ineq_fail",
             "unbounded_N", "unbounded_N_minimal", "minimal_refutations",
             "arc_present", "b0_structural", "b1_candidates", "b1_site_killed",
             "b1_refutations", "b2_configs", "b2_site_killed",
             "b2_beta_instances", "b2_nonempty_overhang", "b2_gap_instances",
             "b2_leaf_refutations", "b3_site_killed", "b3_gap_instances",
             "b3_leaf_refutations", "truncated", "elapsed", "note"]


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Bounded adversary search for the Greendlinger residuals.")
    ap.add_argument("--mode", default="both",
                    choices=["A", "B", "both", "selftest", "verify"])
    ap.add_argument("--alphabet", type=int, default=2)
    ap.add_argument("--min-relator-length", type=int, default=1)
    ap.add_argument("--max-relator-length", type=int, default=2)
    ap.add_argument("--max-relators", type=int, default=1)
    ap.add_argument("--max-conjugator-length", type=int, default=2)
    ap.add_argument("--minimality-cap", type=int, default=3)
    ap.add_argument("--lams", default="1/6,1/7,1/8")
    ap.add_argument("--workers", type=int, default=0)
    ap.add_argument("--out", default="")
    ap.add_argument("--limit-relator-sets", type=int, default=0)
    ap.add_argument("--limit-reps", type=int, default=40)
    ap.add_argument("--shard", type=int, default=0)
    ap.add_argument("--num-shards", type=int, default=1)
    ap.add_argument("--time-budget", type=float, default=600.0)
    ap.add_argument("--max-witnesses", type=int, default=50)
    ap.add_argument("--max-tail-pairs", type=int, default=400000)
    ap.add_argument("--b3", action="store_true",
                    help="also run the spectator-factor leaf search (B3): the "
                         "same overhang question at a two-factor tail, where "
                         "the right disjunct is genuinely available")
    ap.add_argument("--b3-spectator-conjugator-length", type=int, default=0,
                    help="conjugator cap for the B3 spectator factor")
    ap.add_argument("--verify-json", default="")
    a = ap.parse_args(argv)

    lams = [Fraction(s) for s in a.lams.split(",") if s.strip()]
    cfg = {
        "alphabet": a.alphabet, "minlen": a.min_relator_length,
        "maxlen": a.max_relator_length, "max_relators": a.max_relators,
        "cmax": a.max_conjugator_length, "min_cap": a.minimality_cap,
        "lams": lams, "limit_families": a.limit_relator_sets,
        "limit_reps": a.limit_reps, "shard": a.shard,
        "num_shards": a.num_shards, "time_budget": a.time_budget,
        "max_witnesses": a.max_witnesses, "max_tail_pairs": a.max_tail_pairs,
        "b3": a.b3, "b3_cmax": a.b3_spectator_conjugator_length,
        "modes": ["A", "B"] if a.mode == "both" else [a.mode],
    }

    if a.mode == "selftest":
        return selftest(cfg)
    if a.mode == "verify":
        return verify(a.verify_json, cfg)

    families = relator_families(cfg)
    print("families: %d (alphabet %d, relator length %d..%d, size <= %d)"
          % (len(families), a.alphabet, a.min_relator_length,
             a.max_relator_length, a.max_relators), file=sys.stderr)
    if not families:
        print("no family satisfies the metric condition in this range; see "
              "MODELLING DECISIONS note 6 in the header", file=sys.stderr)
        return 0

    tasks = [(i, rel, lam, ss, cfg)
             for i, (rel, lam, ss) in enumerate(families)]
    workers = a.workers or (os.cpu_count() or 1)
    rows, witnesses = [], []
    if workers > 1 and len(tasks) > 1:
        with mp.Pool(workers) as pool:
            for r, w in pool.imap_unordered(run_family, tasks, chunksize=1):
                rows.extend(r)
                witnesses.extend(w)
    else:
        for task in tasks:
            r, w = run_family(task)
            rows.extend(r)
            witnesses.extend(w)
    rows.sort(key=lambda r: (r["idx"], r["mode"]))

    out = a.out or "greendlinger_sweep"
    with open(out + ".tsv", "w") as fh:
        fh.write("\t".join(A_COLUMNS) + "\n")
        for r in rows:
            fh.write("\t".join(str(r.get(k, "")) for k in A_COLUMNS) + "\n")
    with open(out + ".witnesses.json", "w") as fh:
        json.dump({"config": {k: (str(v) if isinstance(v, Fraction) else
                                  [str(x) for x in v] if k == "lams" else v)
                              for k, v in cfg.items() if k != "modes"},
                   "witnesses": witnesses}, fh, indent=1)

    totals = {}
    for r in rows:
        for k in A_COLUMNS[5:-2]:
            v = r.get(k, 0)
            if isinstance(v, int):
                totals[k] = totals.get(k, 0) + v
    print("wrote %s.tsv (%d rows) and %s.witnesses.json (%d witnesses)"
          % (out, len(rows), out, len(witnesses)))
    print("totals: " + "  ".join("%s=%d" % kv for kv in sorted(totals.items())
                                 if kv[1]))
    return 0


def verify(path, cfg):
    """Re-check recorded witnesses at the current --minimality-cap."""
    if not path:
        print("--mode verify needs --verify-json PATH", file=sys.stderr)
        return 2
    with open(path) as fh:
        blob = json.load(fh)
    nletters = 2 * cfg["alphabet"]
    bad = 0
    for w in blob["witnesses"]:
        relators = [bytes.fromhex(h) for h in w["relators"]]
        S = symmetrization(relators)
        sset = frozenset(S)
        expr = []
        for a, b in (("c", "t"), ("c2", "t2"), ("c3", "t3"), ("c_prime", "t_prime")):
            if a in w and b in w:
                expr.append((bytes.fromhex(w[a]), bytes.fromhex(w[b])))
        if not expr:
            continue
        ok, reason, cap = is_minimal_conj_expr(expr, S, sset, cfg["min_cap"],
                                               nletters, {})
        status = "OK" if ok else "FAILS(%s)" % reason
        if not ok:
            bad += 1
        print("%s %s cap=%d %s" % (w.get("mode"), w.get("kind"), cap, status))
    print("re-checked %d witnesses at cap %d; %d no longer minimal"
          % (len(blob["witnesses"]), cfg["min_cap"], bad))
    return 1 if bad else 0


# ---------------------------------------------------------------------------
# 11.  Selftest -- the only thing meant to be run outside the cluster.
# ---------------------------------------------------------------------------


def selftest(cfg):
    fails = []

    def check(name, cond):
        if not cond:
            fails.append(name)

    a, A, b, B = bytes([0]), bytes([1]), bytes([2]), bytes([3])
    check("invrev involutive", invrev(invrev(a + b)) == a + b)
    check("invrev ab", invrev(a + b) == B + A)
    check("reduced", is_reduced(a + b) and not is_reduced(a + A))
    check("cyc reduced", is_cyclically_reduced(a + b)
          and not is_cyclically_reduced(a + b + A))
    check("mul cancels", mul(a + b, B + A) == b"")
    check("rotate", rotate(a + b, 1) == b + a and rotate(a + b, 3) == b + a)
    check("palindrome", palindrome(a, b) == a + b + A)

    # symmetrization of {ab} is its four rotations/inverses, and it is C'(1/6):
    # no two of them share a first letter, so the only piece is the empty word.
    S = symmetrization([a + b])
    check("sym size ab", len(S) == 4)
    check("ab is C'(1/6)", metric_small_cancellation(S, Fraction(1, 6)))
    check("aab is not C'(1/6)",
          not metric_small_cancellation(symmetrization([a + a + b]),
                                        Fraction(1, 6)))

    # Header note 6: in the band 3..12 over Fin 2 every C'(1/6) one-relator
    # family is a proper power, and the aperiodic ones are absent.
    reps_small = canonical_reps(1, 2, 4, 0, 1)
    check("small reps nonempty", len(reps_small) > 0)
    for L in range(3, 9):
        for w in cyclically_reduced_words(L, 4):
            if not metric_small_cancellation(symmetrization([w]), Fraction(1, 6)):
                continue
            period = next(p for p in range(1, L + 1)
                          if L % p == 0 and w == w[:p] * (L // p))
            if period == L:
                fails.append("aperiodic C'(1/6) family at |r|=%d: %s"
                             % (L, w.hex()))
            if len(symmetrization([w])) != 2 * period:
                fails.append("symmetrization size at %s" % w.hex())

    # conjEval reduces; the palindrome is its reduced word only when reduced.
    check("conjEval palindrome", conj_eval([(a, b)]) == palindrome(a, b))
    check("conjEval reduces", conj_eval([(a, b + a)]) == a + b)
    sset = frozenset(S)
    check("one-factor exact", min_weight_one_factor(palindrome(a, a + b), sset) == 1)
    check("one-factor absent", min_weight_one_factor(a + a, sset) is None)

    # A one-factor expression is always minimal, which is what the B0 witness rests on.
    ok, reason, _cap = is_minimal_conj_expr([(b"", a + b)], S, sset, 2, 4, {})
    check("one factor minimal (%s)" % reason, ok)

    # The site predicate is vacuous at the empty expression, which is what makes
    # the StoppingAlternativeBetaSharp witness free (header note 4).
    check("no site at e=[]", conjugator_absorbed_site(a, b, a + b, []) is None)

    # A tiny end-to-end pass over the smallest families.
    tiny = dict(cfg)
    tiny.update({"alphabet": 2, "minlen": 1, "maxlen": 2, "max_relators": 1,
                 "cmax": 1, "min_cap": 1, "limit_families": 4,
                 "time_budget": 20.0, "modes": ["A", "B"]})
    fams = relator_families(tiny)
    check("tiny families found", len(fams) > 0)
    if fams:
        rows, wit = run_family((0, fams[0][0], fams[0][1], fams[0][2], tiny))
        check("tiny run produced rows", len(rows) == 2)
        check("B0 witness present",
              any(w["mode"] == "B0" for w in wit) or rows[1]["b0_structural"] == 0)

    if fails:
        print("SELFTEST FAILURES:")
        for f in fails:
            print("  " + f)
        return 1
    print("selftest OK (%d families in the tiny range)" % len(fams))
    return 0


if __name__ == "__main__":
    sys.exit(main())
