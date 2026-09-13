---
rg: 2
id: toms-line-subalgebra-has-no-nonconstant-continuous-rank
kind: claim
title: In Toms's non-simple limit no Cuntz-increasing realizer of a non-constant continuous rank is block-diagonal from some stage on, so the line subalgebra has no non-constant continuous rank
distinct_from:
  toms-monotone-block-rounding-obeys-a-miranda-granularity-bound: that bounds sharpening only while the number of copies stays below range/eps_n; this removes that restriction through a robust Poincare-Miranda point, and so rules block-diagonal realizers out entirely.
  doubling-ah-finite-stage-continuous-ranks-are-constant: that excludes finite-stage elements and orthogonal sums of them; this excludes every Cuntz supremum whose containments never move support between copies, including all of the line subalgebra.
  toms-schubert-algebra-continuous-ranks-are-constant: that conjectures constancy of all continuous ranks; this proves it for block-diagonal realizers, without the twists, and leaves exactly the realizers that transport support between copies.
---

Let `A = lim (A_N, phi_N)` be the non-simple limit of Toms's Section 4
(arXiv:2606.12188v2), `r_N = rank q_N`. For `x in X_N` let `tau_x` be the point
trace of Lemma 2, extended beyond stage `N` with fixed projective coordinates,
so `x -> tau_x` is continuous. For `M > n` let `Q_1..Q_K`, `K = 2^(M-n)`, be the
(amplified) copy projections of `phi_(n,M)`.

**Theorem.** Let `f` be finite and continuous on `T(A)`. Let `a_m in M_infinity(A_(N_m))_+`
be Cuntz-increasing with `d(a_m) -> f` uniformly, `eps_m = sup_tau (f - d(a_m))`,
and write `R_m` for the fibre ranks. Suppose that for some `n` the containments
into every later stage are **block-diagonal with blockwise domination**:
`a_M = sum_b Q_b a_M Q_b` and `rank (Q_b a_M Q_b)(w) >= R_n(w^(b))`.
If `range_n := max_(X_n) f(tau_x) - min_(X_n) f(tau_x) >= 3 eps_n`, then

```text
eps_M >= 1/(2 r_n)      for every M > n.
```

**Corollary 1.** Such a sequence can realize only a constant `f`. If `f` is
non-constant, then `f(tau_x) != f(tau_y)` for some point traces, so `range_n`
stays bounded below while `eps_n -> 0`. Any `n` with `range_n >= 3 eps_n` then
gives `eps_M >= 1/(2 r_n)` for all `M > n`, which contradicts `eps_M -> 0`.

**Corollary 2 (refutation).** Take the line subalgebra `D` of
`toms-diagonal-subalgebra-supports-a-nonconstant-continuous-rank`. No `a in D_+`
has a finite, continuous, non-constant rank function on `T(A)`. That claim is
false.

**Mechanism (the brief's monotone rounding, made exact).**
- *Budget.* Blockwise domination plus the two uniform bands give
  `sum_b (rank_b - R_n(w^(b))) <= K r_n eps_n` at every stage-`M` point.
- *Robust all-wall point.* Put every copy on a path from a minimum `x_min` to a
  maximum `x_max` of `f(tau_x)`. Let `V_b` be the set where copy `b` has rank at
  least `R_n(x_max)`. A Poincare–Miranda degree argument with `min(u_b, t_b)`
  produces a limit point `t*` of `∩_b V_b` where every copy is either on a wall
  or sits at its own minimum while already inside `V_b`.
- *Slack runs out.* Copies of the second kind each spend at least
  `R_n(x_max) - R_n(x_min) >= 2 r_n eps_n` of the budget, so at most half the copies
  are of that kind. The other half jump at once, and the rank band must absorb
  `K/2` lines.

**What survives.** A realizer of a non-constant continuous rank in `A` must,
for every `n`, have a later containment that is not block-diagonal. So it
transports support **between copies**, through sections of the twisted Hom
bundles `gamma_b tensor gamma_b'^*`. By
`toms-twisted-swap-pairs-are-totally-degeneracy-forcing`, transports made
uniformly across copies lose everything at one point. What is left open is
realizers whose transports are copy-dependent.

**Model test.**
- *Independence of copies is load-bearing.* The diagonal quotient identifies
  all copies. There the path product does not exist, and the image of `D` does
  realize `tau(h)` (`toms-diagonal-quotient-has-nonconstant-continuous-ranks`).
- *Block-diagonality is load-bearing.* In a stable-rank-one Villadsen-type
  tower all ranks occur (Thiel), through Cuntz transports that rotate support
  between copies. The theorem does not forbid those.
- *The target must vary.* Constant `f` is realized by projection sums, which are
  block-diagonal. There `range_n = 0` and the hypothesis fails.

Proof: `toms-line-subalgebra-no-nonconstant-rank-proof`. Internal derivation,
unreviewed. It uses no line-bundle twist, so it holds verbatim in the untwisted
tower.
