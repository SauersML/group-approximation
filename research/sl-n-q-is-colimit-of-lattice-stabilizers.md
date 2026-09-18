---
rg: 2
id: sl-n-q-is-colimit-of-lattice-stabilizers
kind: claim
title: SL_n(Q) is the colimit of the stabilizers of squarefree diagonal lattices over the restricted product of Bruhat-Tits chambers
distinct_from:
  gl-n-q-generated-by-gl-n-z-and-prime-dilations: that gives generators only; this gives a complete presentation as a colimit of copies of SL_n(Z) and their intersections, uniform in the prime.
  elementary-groups-over-polynomial-s-integers-are-fp: that is finite presentation of one E_n(Z[1/m][t]) through Steinberg groups and K_2; this presents the non-finitely-generated SL_n(Q) through lattice stabilizers, with no K_2 input.
artifacts:
  - research/artifacts/gq-gq-k2-q-uniformity.md
---

**OPEN (proof written, two textbook imports not yet quoted at source).** The
argument is in §2 of the artifact and below. It becomes ESTABLISHED once a
referee confirms imports (I2) and (I3) verbatim. For `n = 2` and one prime it
is Serre's amalgam `SL_2(Z[1/p]) = SL_2(Z) *_{Γ_0(p)} SL_2(Z)^{diag(1,p)}`
(Serre, *Trees*, Ch. II §1.4).

**Statement.** Let `n >= 2`. For a vector `c = (c_1,...,c_n)` of squarefree
positive integers with `1 = c_1 | c_2 | ... | c_n` put
`L_c = c_1 Z ⊕ ... ⊕ c_n Z` and `Γ_c = SL(L_c) = diag(c) SL_n(Z) diag(c)^-1`.
Put `k_p(c) = #{i : p | c_i} in {0,...,n-1}`; then `L_c ⊗ Z_p = Z_p^(n-k) ⊕ (pZ_p)^k`
with `k = k_p(c)`, a vertex of the standard chamber `Δ_p` of the building of
`SL_n(Q_p)`, and `c ↔ (k_p(c))_p` identifies these `c` with the vertices of the
restricted product `∏'_p Δ_p`.
A *cell* is a family `F = (F_p)_p` of nonempty subsets `F_p ⊆ {0,...,n-1}` with
`F_p = {0}` for almost all `p`; its vertices are the `c` with `k_p(c) in F_p` for
all `p`, and `Γ_F = ∩_{c vertex of F} Γ_c`.

Then `SL_n(Q)` is the colimit (amalgamated sum) of the diagram of groups
`{Γ_F}` indexed by the cells `F`, ordered by reverse inclusion, with inclusion
maps.
Every `Γ_F` is a congruence subgroup of a conjugate of `SL_n(Z)` defined by
conditions modulo the primes dividing `c_n` for `c in F`, and the diagram is the
restricted product over primes of one local diagram of the same shape (the
faces of an `(n-1)`-simplex).

**Proof sketch.** Fix a finite set `S` of primes and `Γ_S = SL_n(Z[1/S])`.
1. (Elementary) `Z[1/S]` is dense in `∏_{p in S} Q_p`, so the closure of `Γ_S`
   in `G_S = ∏_{p in S} SL_n(Q_p)` contains every elementary matrix, hence is
   `G_S`. Point stabilizers of `G_S` on `X_S = ∏_{p in S} X_p` are open, so
   `Γ_S` has the same orbits as `G_S`.
2. (I1, standard) `G_S` acts on `X_S` type-preservingly and transitively on
   chambers, so the product `C_S` of the standard chambers is a strict
   fundamental domain for `Γ_S`, and each cell stabilizer fixes the cell
   pointwise. The vertex stabilizers in `Γ_S` of `C_S` are the `Γ_c` with all
   `c_i` supported on `S`.
3. (I2) Euclidean buildings are CAT(0), hence contractible; so is `X_S`.
4. (I3) A group acting without inversions on a simply connected complex with a
   simply connected strict fundamental domain `Y` is the colimit of the cell
   stabilizers of `Y` (Soulé 1973; Bridson–Haefliger Part II Ch. 12). So
   `Γ_S = colim_{F ⊆ C_S} Γ_F`.
5. For `S ⊆ S'`, the faces of `C_S` are the faces of `C_{S'}` whose coordinates at
   `S' \ S` are the base vertex, with the same stabilizers. Colimits commute with
   the directed union of these diagrams, and `SL_n(Q) = ∪_S Γ_S`. ∎

## Attempts

None beyond this proof. Referee request: quote (I2), (I3) at source.
