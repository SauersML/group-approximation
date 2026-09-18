---
rg: 2
id: bk-unkilled-classes-diverge-past-index-shifts
kind: claim
title: An unkilled K_0-class diverges along every exhaustion and every strongly convergent almost-invariant sequence of an essential representation, and a Cuntz-pair twist shifts it only by a constant
distinct_from:
  stw07-unkilled-classes-are-model-one-signed: that gives the sign trichotomy for models one term at a time; this proves that nested exhaustions of one essential representation have monotone divergent values for an unkilled class, and that twisting the representation by a Cuntz pair shifts them only by a constant.
  stw07-trace-invisible-classes-carry-hahn-banach: that makes every class invisible to traces (scale k_n); this adds the lower wall at scale 1, so an unkilled trace-invisible class lives strictly between index scale and trace scale.
  k0-hahn-banach-for-boundary-singular-classes: that is the open statement that singular classes are killed; this is an obstruction to proving it by exhaustion or index-twist constructions, not a proof or a refutation.
---

**ESTABLISHED (lane proof in the `-proof.md` artifact; not externally
reviewed).**  Obstruction.

Let `A` be separable, unital and quasidiagonal, and let `pi: A -> B(H)` be a
faithful essential unital representation. A *QD exhaustion* is a sequence of
finite-rank projections `P_1 <= P_2 <= ...` with `P_n -> 1` strongly and
`||[P_n, pi(a)]|| -> 0`. Write `v_n(x)` for the eventual rank value on
`x in K_0(A)` of the compression model `P_n pi(.) P_n`, and `k_n = rank P_n`.
"Killed" means that some faithful model has value `0` (case 1 of
`stw07-unkilled-classes-are-model-one-signed`).

1. **Monotone divergence.** If `x` is not killed, then along every QD
   exhaustion of every faithful essential `pi`, `|v_n(x)|` is eventually
   nondecreasing and tends to infinity with a fixed sign. Equivalently, if
   some exhaustion has `liminf |v_n(x)| < infinity`, then `x` is killed.
2. **Index shift is a constant.** If `pi'` is a unital representation with
   `pi'(a) - pi(a)` compact for all `a` (a Cuntz pair), then every QD
   exhaustion of `pi` is one of `pi'`, and `pi'` is faithful and essential.
   Moreover `v'_n(x) = v_n(x) - c(x)` for all large `n`, where
   `c(x) = ind(pi(p), pi'(p)) - ind(pi(q), pi'(q))` for `x = [p]-[q]`. This
   is the essential-codimension pairing of `x` with `[pi, pi'] in KK(A, C)`.
3. **Trace wall.** If every limit trace of `tr_(k_n) o P_n pi P_n` vanishes on
   `x`, then `v_n(x) = o(k_n)`.
4. **Moves keep the sign.** Enlarging the exhaustion, or forming a direct sum
   with another exhaustion model, changes `v_n(x)` by eventually nonnegative
   amounts when `x` is in the nonnegative case.
5. **Uniform positivity and the strong-convergence wall.** If `x` is not
   killed (say nonnegative), there are a finite `F subset A` and `epsilon > 0`
   such that every `(F, epsilon)`-multiplicative u.c.p. map `A -> M_k` is
   `>= 0` on `x`, and `> 0` if it is also `(F, epsilon)`-isometric. Hence,
   with `delta_0` depending only on `(F, epsilon)`: every finite-rank
   projection `Q` that almost commutes with `pi` on `F` and satisfies
   `||(1-Q)P_N|| < delta_0` for a large exhaustion stage `P_N` has value
   `>= v_N`. So almost-commuting finite-rank `Q_n -> 1` strongly have values
   tending to infinity, whether or not they are nested. Equivalently, if such
   a sequence has bounded values along a subsequence, then `x` is killed.

**Class killed.** Suppose `x` is singular (`Zx cap K_0^+ = 0`), trace-invisible
and not killed, so that it is a failure of K_0-Hahn--Banach. Then along every
exhaustion of every essential representation, the value germ satisfies
`1 << v_n(x) << k_n`. So the following constructions cannot produce the
zero-value faithful model that K_0-Hahn--Banach requires:

- compressions along a nested exhaustion of any faithful representation,
  whether from Voiculescu or Arveson quasicentral approximate units;
- such compressions after any KK(A,C) or Cuntz-pair twist, direct-sum
  absorption or enlargement of the filtration;
- non-nested almost-invariant subspaces converging strongly to `1`, or
  approximately containing arbitrarily large exhaustion stages;
- constructions controlled only through limit traces, such as full-map or
  trace-realisation existence theorems and trace pushouts.

Exactly where each fails:

- **Index twists.** The correction `c(x)` is a fixed integer, while the
  quantity it would have to cancel is unbounded.
- **Enlargements, absorption and strong convergence.** They only add blocks
  that are almost invariant, and those are nonnegative by uniform positivity
  (item 5).
- **Trace methods.** They see only `v_n/k_n -> 0`, which is the same data as
  for `x = 0`.

A proof of K_0-Hahn--Banach, and so of Problem VII through Brown--Dadarlat
Theorem 4.11, must therefore kill singular classes with *non-nested*
sequences of almost-commuting finite-rank projections `Q_n`. By Voiculescu's
theorem every faithful model is of this form. Killing needs `Q_n` that do not
converge strongly to `1`, and that for every large `N` stay at distance
`delta_0` from containing `P_NH`; `delta_0` is independent of `N`. So killing
subspaces must escape every exhaustion at a uniform angle. Such escaping
killing sequences do exist for killed classes (Voiculescu lets them go weakly
to `0`), so this is where a proof must do its work. The intermediate-scale germ
`v_n(x) mod O(1)`, which lies at scale `o(k_n)`, is the invariant that
index-theoretic and tracial approaches both miss.

Calibration (in the proof artifact):

- `A = C`, `x = [1]`: `v_n = k_n -> infinity`, and `x` is not killed.
- `A = C + C`, `x = [e_1]-[e_2]`: a balanced exhaustion has bounded values and
  kills `x`.
- A Cuntz pair that trades one copy of `ev_1` for one of `ev_2` shifts
  `v_n([e_1])` by exactly `-1`.
