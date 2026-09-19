---
rg: 2
id: fpbs-stationary-set-relative-gap-universal
kind: claim
title: On every nonamenable Cayley graph some slightly supercritical cluster of the origin is met only finitely often by some independent walk range or aperiodic subrelation class
distinct_from:
  fpbs-green-visit-criterion-universal: that fixes simple random walk and asks for finite expected visits; this lets the step law vary, or replaces the walk by any aperiodic subrelation class, and asks only for almost surely finite visits, so that claim implies this one.
  fpbs-percolation-schreier-kesten-gap: that asks for a gap along deterministic non-co-amenable subgroups, which exist only outside the all-subgroups-co-amenable class; this allows random sets independent of the percolation, which exist on every group, including Tarski monsters, where every subgroup is blind.
  fpbs-relative-gap-along-every-amenable-subgroup-universal: that is a gap along every amenable subgroup; this is existence of one random set with finite visits at one supercritical parameter.
  fpbs-benjamini-schramm-universal: that is nonuniqueness at some p above p_c; this is a certificate for it through fpbs-stationary-set-recurrence-separates, and it is equivalent to the goal only under uniform connectivity decay in the nonuniqueness phase, which is not claimed.
artifacts:
  - research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md
---

**OPEN.** Let `G = Cay(Gamma,S)` be nonamenable. Then there are `p > p_c(G)`
and an independent stationary set `A` such that `V < infinity` almost surely
under `P_p`. Here `A` is of one of two types:

* **(W)** the path of an i.i.d. walk with some step law `mu` on `Gamma`, with
  `V = #{n : X_n in C_e}`;
* **(R)** the set `A(y) = {g : (g^{-1}y, y) in R'}` for some aperiodic Borel
  subrelation `R'` of the orbit relation of some free pmp action, with
  `V = |C_e ∩ A(y)|`.

In both cases `A` is independent of the percolation, and the definitions are
those of `fpbs-stationary-set-recurrence-separates`.

**What it gives.** `fpbs-stationary-set-recurrence-separates` turns it into
`p_c < p <= p_u` (route `fpbs-bs-via-stationary-set-relative-gap`).

**Where it sits.** Every sufficient kernel of the following two kinds implies
it, so it is weaker than each of them (Section 6 of the artifact):

* **Green-visit kernels.** `fpbs-green-visit-criterion-universal` (family (W)
  with simple random walk, expectation form), and through it PB, NC, IS,
  `p_c < p_(2->2)` and `tau_p in l2`.
* **Relative-gap kernels.** Every relative gap `p_c(G) < p_c(I;G)` along an
  infinite subgroup (family (R) with the orbit relation of `I`), including
  `fpbs-percolation-kesten-normal-gap` and
  `fpbs-percolation-schreier-kesten-gap` wherever they apply.

It is also implied by uniform connectivity decay `tau_p(e,.) -> 0` at a single
`p > p_c`, by `fpbs-connectivity-decay-gives-heavy-walk-green-visits`.

**Sanity check (trees).** On `T_d`, `d >= 3`, simple random walk has
`E V = g(e)(1 + (d/(d-1)) p/(1-p)) < infinity` for all `p < 1 = p_u`. So the
simplest member is lossless there.

## Attempts

* **Soft supercritical inputs (obstruction, 2026-09-19, swarm-0917 w18c).**
  `fpbs-soft-collapse-kills-stationary-set-gap-proofs` (ESTABLISHED) shows
  that on every graph with invariant sparse spines, the soft collapse family
  meets every independent stationary set infinitely often for every
  `t > p_c`. This covers every step law and every aperiodic subrelation.
  * **Where it dies:** the passage from Bernoulli data at `p_c` to
    `V < infinity` at `p_c + delta`.
  * **Invariant:** invariant sparse spines.
  * So freeing the random set from being a subgroup does not buy a soft
    proof. A proof must use BK or Russo above `p_c`, deletion tolerance,
    Harris--FKG, or the product structure.
* **Free step law, sparse walks (reduction, 2026-09-19, swarm-0917 w18c).**
  Let the step law depend on `p`. Heavy mixtures of uniform measures on
  fast-growing balls give `E V < infinity` as soon as `tau_p(e,.) -> 0`
  uniformly at infinity (`fpbs-connectivity-decay-gives-heavy-walk-green-visits`).
  * **Where it dies:** the input is uniform decay at some `p > p_c`. That
    already gives nonuniqueness at `p` through `tau >= theta^2`, so the
    reduction is circular for the goal.
  * What it does show is ordering: the (W) family reaches the decay threshold
    `p_dec`, so any future proof of decay past `p_c` closes this hole.
* **Subgroup members on the hard class (2026-09-19, swarm-0917 w18c).** On
  `fpbs-all-infinite-subgroups-co-amenable-class-nonuniqueness`, including
  Kazhdan Tarski monsters, every subgroup member of (R) is empty, by
  `fpbs-co-amenable-subgroup-relative-threshold-is-pc`.
  * **Where it dies:** for subgroups, at condition 1, for every subgroup at
    once.
  * **What survives:** the walk ranges and the non-subgroup relations, for
    instance hyperfinite ones. The blindness proof needs a Følner sequence of
    the Schreier graph `I\Gamma`, and neither family has one. For a
    hyperfinite subrelation of a free pmp action of a nonamenable group, an
    invariant mean on classes would make the orbit relation amenable.
  * This is recorded as a remark only. No blindness result for these
    families is known, and no gap for them is known on that class.
  * Unlike the subgroup relative-threshold kernels, this hole has
    relative-threshold members that are not known to be empty on Tarski
    monsters.
