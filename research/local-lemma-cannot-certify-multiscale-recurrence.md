---
rg: 2
id: local-lemma-cannot-certify-multiscale-recurrence
kind: claim
title: Over the uniform product measure, the asymmetric local lemma cannot certify recurrence at infinitely many scales alongside any translation-invariant positive-probability constraint, so it cannot produce minimal subshifts on any infinite group
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `decidable-fp-groups-have-effective-minimal-free-subshifts`, `free-minimal-subshifts-with-computable-moduli-exist`.

**Status.** Lane proof, elementary, not reviewed. This is a **method-kill** for gate
G1/(M2) of the master route. It says nothing against (M2) itself. No priority is claimed.

## Setting

- `G` is an infinite finitely generated group with balls `B(r)`, `A` is a finite alphabet,
  and `μ` is the uniform product measure on `A^G`. The action is `(g·x)(h) = x(hg)`.
- An *event* is a clopen set `E ⊆ A^G` with a finite support `S(E)`.
- An *LLL certificate* for a countable family `𝓔` of events consists of:
  - the dependency graph with `E ∼ F` iff `S(E) ∩ S(F) ≠ ∅`;
  - weights `x_E ∈ [0,1)` such that `μ(E) ≤ x_E ∏_{F∼E, F≠E}(1 − x_F)` for every `E`.
- The local lemma plus compactness then gives a configuration avoiding every `E ∈ 𝓔`.
  This is the "local lemma plus compactness" method listed in
  `free-minimal-subshifts-with-computable-moduli-exist`.

## Theorem

Suppose `𝓔` contains the following.
1. **A positive-density family.** All translates `F·g` (`g ∈ G`) of one event `F` with
   `μ(F) = p > 0`.
2. **Recurrence at infinitely many scales.** For infinitely many `r`, a set `Q_r` of
   patterns on `B(r)` and a radius `R_r`, such that `𝓔` contains the event
   `E_r = {x : no q ∈ Q_r occurs at any h ∈ B(R_r)}`.
   - Here "`q` occurs at `h`" means `x(ηh) = q(η)` for all `η ∈ B(r)`.
   - The density `δ_r = |Q_r|·|A|^{-|B(r)|}` must satisfy `δ_r|B(r)|² → 0` along these `r`.

Then `𝓔` has **no** LLL certificate.

**When the density hypothesis holds.**
- A single pattern (`δ_r = |A|^{-|B(r)|}`) satisfies it.
- So does the set of all `B(r)`-patterns of any fixed subshift `X ≠ A^G`.
  - Suppose `X` forbids a pattern on `B(r_0)`. A maximal `2r_0`-separated subset of
    `B(r − r_0)` gives `s ≥ |B(r − r_0)|/|B(2r_0)|` disjoint `B(r_0)`-balls inside `B(r)`.
  - Hence `δ_r ≤ (1 − |A|^{-|B(r_0)|})^s`. Since `|B(r)| ≤ |B(r_0)||B(r − r_0)|`, this beats
    `|B(r)|²`.
- This covers the defining events "some `L_n`-window within `R_n − m_n`" of the tower
  subshifts, whenever the tower is not the full shift.

## Proof

If `p = 1`, the inequality for `F` would need `x_F ≥ 1`, which no certificate allows. So
assume `p < 1`, which makes `S(F)` nonempty. Put `k = |B(r)|`, `N = |B(R_r)|` and
`M = |S(E_r)|`. Since `S(E_r) = B(r)B(R_r)`, we have `M ≥ max(k, N)`.

- **Positive-density weights are bounded below.** For every translate,
  `p = μ(Fg) ≤ x_{Fg}·∏ ≤ x_{Fg}`.
- **Upper bound on `μ(E_r)`.**
  - Put `c = |S(F)|²`. At least `M/c` distinct translates `Fg` meet `S(E_r)`:
    - each site `u` lies in some `S(F)g`;
    - each `g` is reached from at most `|S(F)|` sites;
    - `Fg = Fg'` forces `S(F)g'g^{-1} = S(F)`, which allows at most `|S(F)|` values of `g'`.
  - At most one of these translates is `E_r` itself.
  - So the certificate inequality for `E_r` gives
    `μ(E_r) ≤ (1 − p)^{M/c − 1} ≤ exp(−p(M/c − 1))`.
- **Lower bound on `μ(E_r)`.**
  - Let `O_h` be the event that some `q ∈ Q_r` occurs at `h`. Patterns on the same support
    are disjoint events, so `μ(O_h) = δ_r`.
  - `O_h` shares coordinates only with `O_{h'}` for `h' ∈ B(2r)h`, and `|B(2r)| ≤ |B(r)|²`.
  - Put `y = eδ_r`. For all large `r` in the family, `y|B(2r)| ≤ 1/2`, so
    `(1 − y)^{|B(2r)|} ≥ 1/e`, and the symmetric LLL with weight `y` applies to
    `{O_h : h ∈ B(R_r)}`.
  - Its lower bound gives `μ(E_r) ≥ (1 − y)^N ≥ exp(−2eδ_r N)`.
- **Comparison.** The two bounds give `2eδ_r N ≥ p(M/c − 1)` for infinitely many `r`.
  - If `N ≥ k`, then `M ≥ N`, so `2eδ_r ≥ p/c − p/k`.
  - If `N < k`, then `M ≥ k`, so `2eδ_r k ≥ p(k/c − 1)`.
  - Both fail for large `r`, because `k = |B(r)| → ∞` (`G` is infinite) and
    `δ_r k ≤ δ_r k² → 0`. ∎

## Consequences for (M2) and (N)

**A subshift that is minimal by its definition is outside the method.**
- Consider any effectively closed subshift whose minimality is written into its defining
  constraints. Examples:
  - the tower subshift `Y = {z : every g has an L_n-window within R_n − m_n}` of
    `decidable-fp-groups-have-effective-minimal-free-subshifts`, Attempt 3;
  - "every locally admissible `r`-pattern occurs in every `R_r`-ball".
- Such a subshift contains recurrence events at all scales. It also contains a
  positive-density family: the recurrence events of the smallest scale, or any freeness
  constraint. So no uniform-measure LLL proves it nonempty.

**This is a new kill, separate from path selection.**
- Attempt 4 of the (M2) node puts "local lemma plus compactness" among the methods that
  reach (N) and die only at path selection.
- The theorem sharpens this: over the uniform product measure the local lemma does not even
  reach (N).
- Aubrun–Barbieri–Thomassé (arXiv:1507.03369, context only) use the LLL for *strong
  aperiodicity*. That needs only positive-density events, and is consistent with the theorem.

**The machine-labelling angle dies here too.** The idea was to take configurations to be
labellings that a word-problem decider certifies as locally consistent, and let randomness
fill in the rest.
- Local certification gives effective closedness.
- By the theorem, randomness cannot add minimality.
- So the decider can enter an (M2) proof only by computing a *deterministic hierarchy*, as in
  the greedy ball-copy skeleton of Attempt 2. Randomness can at most choose within finite
  libraries inside that hierarchy.

**Not covered.** Lopsided and cluster-expansion (Shearer) variants are not checked. Neither
are non-product measures. A hierarchical measure that draws each scale-`r` patch from a
library of size `N_r` escapes the computation, because then a patch recurs at rate
`≈ 1/N_r` per tile instead of `|A|^{-|B(r)|}` per site.

## Lesson for general BH

- **Recurrence is anti-local.** Its success rate per unit volume, `|A|^{-|B(r)|}`, dies with
  the scale, while every positive-density constraint (freeness included) costs a fixed amount
  per unit volume. So minimality cannot be bought with independent randomness.
- **Minimality must be hierarchical.** Entropy has to be lowered scale by scale, with
  finite libraries, substitutions, or Toeplitz and blueprint skeletons.
- **Where this lands on the route.** On groups with no finite quotients (the simple Kazhdan
  inputs), Toeplitz skeletons are also excluded (Lemma T of the (M2) node). What is left for
  G1 is a *computable non-profinite hierarchy*. That is the same kind of object as the rigid
  finite-type codings that the synthesis thesis puts at the crux G2.
- **Practical rule.** Stop spending lanes on uniform-measure local-lemma arguments for (N)
  or (M2). Spend them on computable hierarchies over balls.
