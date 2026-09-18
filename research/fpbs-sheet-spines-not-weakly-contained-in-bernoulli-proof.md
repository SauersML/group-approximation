---
rg: 2
id: fpbs-sheet-spines-not-weakly-contained-in-bernoulli-proof
kind: route
title: The sheet indicator is a nontrivial factor fixed by the nonamenable kernel, and an atomless height law carries Rokhlin towers
target: fpbs-sheet-spines-not-weakly-contained-in-bernoulli
requires:
  - fpbs-quotient-split-not-bernoulli-contained
---

Notation is that of the target. `N = ker pi`. The map `L -> Ĥ` is
measurable, since `Ĥ = {h : pi^-1(h) ⊆ V(L)}` is a countable intersection
of cylinder events. For `gamma in Gamma`,
`V(gamma L) = gamma V(L)` and `gamma pi^-1(h) = pi^-1(h + pi(gamma))`, so

    Ĥ(gamma L) = Ĥ(L) + pi(gamma).                                   (1)

So `Gamma` acts on the factor `Ĥ ∈ 2^Z` through `pi`, by the shift `T`.

**Step 0: `N` is nonamenable.** `Gamma / N ≅ Z` is amenable, and an extension
of an amenable group by an amenable group is amenable. `Gamma` is nonamenable,
so `N` is not amenable.

**Step 1: the factor is nontrivial.** Let `p = P(0 ∈ Ĥ)`. By (1) and
invariance of the law of `L`, `P(h ∈ Ĥ) = p` for every `h`.
- If `p = 0`, then `Ĥ = ∅` a.s.
- If `p = 1`, then `Ĥ = Z` a.s.

Both are excluded by hypothesis, so `0 < p < 1`. The factor
`L -> 1[0 ∈ Ĥ(L)] ∈ {0,1}` is therefore nontrivial (its law is not a point
mass). By (1), `N` acts trivially on it, since `pi(n) = 0`.

**Step 2: not weakly contained in Bernoulli.**
`fpbs-quotient-split-not-bernoulli-contained` (Proposition B) says: let `N`
be a nonamenable normal subgroup of a countable group `Gamma`, and `alpha` a
p.m.p. action of `Gamma` with a nontrivial factor on which `N` acts trivially.
Then `alpha` is not weakly contained in `b_Gamma`.

Apply it to `alpha` = the shift action of `Gamma` on the law of `L`, with the
factor of Step 1. Steps 0 and 1 are exactly its hypotheses, so the process `L`
is not weakly contained in the Bernoulli shift of `Gamma`. This holds with no
condition on atoms.

**Step 3: an atomless height law gives a non-strongly-ergodic process.**
Let `nu` be the law of `Ĥ` on `2^Z`. It is `T`-invariant by (1), and it is
atomless by hypothesis.

*Aperiodicity.* A point of `2^Z` with `T^r x = x` for some `r >= 1` is
determined by `x_0, ..., x_{r-1}`. So the periodic points form a countable
set, and `nu` gives it measure `0`. Hence `T` is an aperiodic automorphism of
`(2^Z, nu)`.

*Rokhlin lemma* (Rokhlin 1948; textbook form in Halmos, *Lectures on
Ergodic Theory*, 1956; section numbers not checked here). This is used only
in its standard form: if `T` is an
aperiodic measure-preserving automorphism of a standard probability space,
then for every `n >= 1` and `delta > 0` there is a measurable `B` such that
`B, TB, ..., T^{n-1}B` are pairwise disjoint and their union has measure
`> 1 - delta`. Ergodicity is not needed.

*Construction.* Fix an even `n` and `delta = 1/n`, and take `B` from the
lemma. Set `D = B ∪ TB ∪ ... ∪ T^{n/2 - 1}B`. Then
`n nu(B) ∈ (1 - 1/n, 1]`, so `nu(D) = (n/2) nu(B) ∈ ((1 - 1/n)/2, 1/2]`. Also
`TD Δ D ⊆ B ∪ T^{n/2}B`, so `nu(TD Δ D) <= 2 nu(B) <= 2/n`. By the triangle
inequality `nu(T^m D Δ D) <= 2|m|/n` for every `m ∈ Z`.

*Pull back.* Let `A_n = {L : Ĥ(L) ∈ D_n}`. Then `P(A_n) -> 1/2`. By (1),
`gamma A_n` is the pullback of `T^{pi(gamma)} D_n`, so
`P(gamma A_n Δ A_n) <= 2|pi(gamma)|/n -> 0` for every `gamma`. So `(A_n)` is
an asymptotically invariant sequence with `P(A_n)(1 - P(A_n)) -> 1/4`, and
the process is not strongly ergodic.

**Remark (atomic case).** Step 3 genuinely needs atomlessness. The referee
example (sheets over `rZ + j`, `j` uniform on `Z/r`, iid connectors) is
strongly ergodic, and the target's statement already excludes it. Step 2
covers it.

**Status.** Step 2 is the imported Proposition B. Step 3 uses only the Rokhlin
lemma, which is textbook. So the target, and with it the last open
prerequisite of `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines-proof`, is
closed. This proof is agent-written and has not been refereed.
