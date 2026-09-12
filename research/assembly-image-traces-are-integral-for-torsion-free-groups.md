---
rg: 2
id: assembly-image-traces-are-integral-for-torsion-free-groups
kind: claim
title: For a torsion-free group the canonical trace is integer-valued on the image of the reduced assembly map
distinct_from:
  kadison-kaplansky-torsion-free: that is the conjecture that the reduced C*-algebra of a torsion-free group has no nontrivial projection; this is the index-theorem fact that traces of assembly-image classes are integers, which gives the conjecture only when assembly is surjective.
  rank-one-lattice-kadison-kaplansky-and-charzero-idempotents: that uses surjective assembly for rank-one lattices to conclude Kadison--Kaplansky; this is integrality of the trace on the assembly image for every torsion-free group, with no surjectivity assumed.
artifacts:
  - research/artifacts/kk-sl3z-congruence-2026-09-12.md
---

**ESTABLISHED (citation).** Let `Γ` be a countable torsion-free discrete group and `τ` the
canonical trace on `C*_r(Γ)`, extended to `K_0` by `τ_*[e] = sum_i τ(e_ii)` for
idempotents `e ∈ M_n(C*_r Γ)`. Then

```text
τ_*( mu_r(x) )  ∈  Z     for every x ∈ K_0^Γ(\underline{E}Γ).
```

**Consequence.** If `mu_r` is surjective, then `τ_*(K_0(C*_r Γ)) ⊆ Z`, and `C*_r(Γ)` has no
projection other than `0` and `1`. This is Proposition 4.20 of the survey below, and
Kaad–Proietti's Corollary 1.6 as used in `rank-one-bcc-implies-charzero-idempotent-proof`.

**Mechanism.**
1. A cycle of the left-hand side is `(Z, ξ)`, with `Z` a proper `Γ`-compact manifold.
2. Since `Γ` is torsion-free, the action is free, so `Z → Γ\Z` is a covering.
3. `mu_r(Z, ξ) = Ind_Γ(D~)` for a `Γ`-invariant elliptic operator `D~` lifted from `D` on
   `Γ\Z`.
4. Atiyah's L²-index theorem gives `τ_*(Ind_Γ(D~)) = Ind(D) ∈ Z`.

**Sources.**
- **Gomez Aparicio–Julg–Valette** (arXiv:1905.10081), §4.5.3, read from the arXiv PDF on
  MSI: "Actually we prove that, assuming Γ to be torsion-free, τ_* is always
  integer-valued on the image of μ_r in K_0(C*_r(Γ)) ... we may appeal to Atiyah's
  L²-index theorem ... τ_*(μ_r(Z, ξ)) = Ind_Γ(D~) = Ind(D). Since Ind(D) ∈ Z, this
  concludes the proof."
- **Kaad–Proietti**, *Index theory on the Miščenko bundle* (arXiv:1807.05757; Kyoto J. Math.
  62 (2022)), abstract: "we give a proof of Atiyah's L²-index theorem in the general
  context of principal bundles over compact Hausdorff spaces. We thereby also reestablish
  that the surjectivity of the Baum-Connes assembly map implies the Kadison-Kaplansky
  idempotent conjecture in the torsion-free case."
- **Not read:** Atiyah's 1976 paper, and the survey's footnote 17. That footnote points to
  Mislin–Valette, Lemma 7.1, for a proof that does not use the L²-index theorem.
