---
rg: 2
id: burau-faithful-iff-faithful-on-noncentral-normal-subgroup-proof
kind: route
title: "Long's theorem for n >= 4 from centralizers of normal subgroups in the mapping class group of the sphere"
target: burau-faithful-iff-faithful-on-noncentral-normal-subgroup
requires: []
artifacts:
  - research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md
---

Full write-up: artifact §2.1–2.2.

**The center is detected.** `det ρ_n(σ_i) = -t`, so `det ρ_n(Δ^{2k}) = t^{k n(n-1)} ≠ 1` for
`k ≠ 0`. Hence `ρ_n` is injective on `Z(B_n) = ⟨Δ²⟩` (Chow).

**Lemma L1.** Let `ρ` be injective on `Z(G)`, and let `N ⊴ G` with `C_G(N) = Z(G)`. If `K = ker ρ`
meets `N` trivially, then `[K,N] ⊂ K ∩ N = 1`, so `K ⊂ Z(G) ∩ ker ρ = 1`.

**Lemma L2.** For `n ≥ 4` and `N ⊴ B_n` noncentral, `C_{B_n}(N) = Z(B_n)`.

Standard inputs:

1. `B_n/Z(B_n) ≅ M`, the stabilizer of a marked point in `MCG(S_{0,n+1})`.
2. Ivanov: a subgroup without pseudo-Anosov elements is finite or has a nonempty natural
   canonical reduction system.
3. Mapping class groups are virtually torsion-free, so torsion subgroups are finite.
4. For `m = n+1 ≥ 5`, `MCG(S_{0,m})` acts faithfully on `PML`, and stable laminations of
   pseudo-Anosovs in any finite-index subgroup are dense.
5. Centralizers of pseudo-Anosov classes are virtually cyclic (McCarthy).

Proof:

- **(a)** A finite normal `T ⊴ M` is centralized by a finite-index subgroup. So each element of
  `T` fixes a dense set of `PML` and is trivial by input 4.
- **(b)** `N̄ = NZ/Z ≠ 1` contains a pseudo-Anosov. Otherwise, by input 2, either `N̄` is finite,
  hence trivial by (a), or its canonical reduction system is an `M`-invariant curve system, which
  a pseudo-Anosov in `M` cannot fix.
- **(c)** Take two independent pseudo-Anosovs in `N̄` (a pseudo-Anosov and a generic conjugate
  of it). The image of any `c ∈ C_{B_n}(N)` centralizes both, so it has finite order by input 5.
  Thus `C_{B_n}(N)/Z` is a normal torsion subgroup of `M`. It is finite by input 3 and trivial by
  (a).

Combining L1 and L2 with the center computation proves the claim. ∎
