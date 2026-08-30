---
rg: 2
id: uniformly-doubled-rordam-steps-force-proper-infiniteness
kind: claim
title: Common tails beat bounded early parts, so uniformly doubled Rordam towers have properly infinite limits
invalidates: [stw99-lxvi-via-dyadic-rordam-tower]
distinct_from:
  dyadic-rordam-tower-realizes-finite-car-corner: that was the paired-step candidate construction for Problem LXVI; this establishes that its halving mechanism (globally duplicated branch lists) forces the seed projection to become properly infinite, refuting the design as stated.
  stw99-lxvi-car-stabilization-destroys-finite-seed: that kills tensorial CAR insertion; this kills the multiset-doubling insertion inside Rordam's line-bundle calculus, a different mechanism with an Euler-theoretic proof.
artifacts:
  - research/artifacts/stw99-lxvi-dyadic-rordam-design-2026-08-30.md
---

Let `B = lim (M(A), ψ̄_n)` be a Rørdam-type tower over `Z = (S²)^∞` with
line-bundle multiset dynamics `α_β(J) = ν_β(J∖E_β) ∪ I_β`, and let `Q` be
the limit of a full direct-sum projection.  Suppose that at some stage `n`
the evolved multiset of `Q` assigns multiplicity at least `M` to `m`
member sets `S_1, …, S_m` of the form `S_j = T ⊔ u_j` with a common tail
`T` and early parts `|u_j| ≤ u`, where `M m > |T| + m u`.  Then the
corresponding subprojection contains a trivial rank-one subbundle, so
`g ≾ Q`; and when such families exist in infinite disjoint supply,
`1 ~ ⊕^∞ g ≾ Q`, and `Q` is properly infinite by Rørdam's Lemma 4.3.

**Consequence.**  Any design in which the halving `Q_k ~ 2Q_{k+1}` is
implemented by steps that duplicate the entire branch list — so that every
class becomes exactly `2^{c(n)}`-divisible with `c(n) → ∞` — and whose
branch list at one fixed early step contains infinitely many branches
with uniformly bounded finite tensor sets produces a properly infinite
`Q_1`.  In the proposed tower, (C2) supplies infinitely many step-1
branches with singleton `I_beta`, so the early parts have size at most
two.  Following one common later history gives a common tail, while the
paired-step multiplicities grow without bound; the hypothesis above is
met in infinitely many disjoint groups of C2 branches.  So the paired-step
dyadic tower
(`dyadic-rordam-tower-realizes-finite-car-corner`) fails as designed, and
`stw99-lxvi-via-dyadic-rordam-tower` is dead.  More broadly: in the
line-bundle Euler calculus, the finiteness certificate (a system of
distinct representatives, Rørdam Prop 3.2/4.5(i)) and the divisibility
demands of a CAR tower meet exactly at the rank-equals-half-dimension
boundary, on opposite sides; every absorption or halving trick crosses it.
A positive solution of Problem LXVI along Rørdam lines must therefore
leave rank-one building blocks: the surviving direction is a tower of
higher-rank blocks `η_m` with `η_m ≅ η_{m+1} ⊕ η_{m+1}` and
`e(η_m) ≠ 0` at every level — Euler classes with all 2-power roots
nonvanishing exist in `H^*((S²)^∞)` (sums of at least `2^m` disjoint
quadratic monomials, e.g. `ε = Σ_t x_{2t−1}x_{2t}` with `ε^r = r!·e_r ≠ 0`),
and the open crux is realizing them by bundles compatible with the
dynamics; recorded in the design dossier.
