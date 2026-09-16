---
rg: 2
id: berend-dual-circle-rokhlin-obstruction-proof
kind: route
title: The dual action is inner on finite-orbit quotients whose stabilizers lie in p Gamma
target: berend-dual-circles-have-infinite-rokhlin-dimension
requires:
  - berend-torus-actions-give-strongly-qd-polycyclic-groups
artifacts:
  - research/artifacts/berend-dual-circle-rokhlin-obstruction-2026-09-16.md
---

The full proof is in the artifact. Write `X = T^3`, and let `B_Y = C(Y) ⋊ Γ`
for a finite orbit `Y` with stabilizer `Λ`.

**Lemma 1 (fixed central sequences).** Let a compact group `K` act on a
σ-unital `I`, and let `π : I → B` be a surjective equivariant map onto a
nonzero unital `B`. Suppose some `s ≠ e` fixes `B_∞ ∩ B'` pointwise. Then
`dim_Rok = dim^c_Rok = ∞`.

- *The comparison map.* The componentwise map `π_∞` induces a unital
  equivariant `F(I,I) → B_∞ ∩ B'`. It kills the annihilator because
  `π(d_0) = 1_B` for some `d_0 ∈ I`. It is unital because the unit of
  `F(I,I)` is the class of an approximate unit `e`, and
  `π_∞(e) = π_∞(e d_0) = 1_B`.
- *The contradiction.* Compose the Rokhlin towers with this map. Choose a
  partition of unity `f_i` with `f_i · Lt_s f_i = 0`. Equivariance and
  fixedness give `ψ_j(f_i)^2 = 0`, hence `1_B = 0`.

**Lemma 2 (inner on the quotient).** Take `χ ∈ Λ^⊥` and set
`c_χ(γ y_0) = χ(γ)`. This gives a well-defined unitary in `C(Y)`, and
`\hat β_χ = Ad(c_χ)` on `B_Y`. So `\hat β_{∞,χ}` fixes
`(B_Y)_∞ ∩ B_Y'`.

**Lemma 3 (explicit torsion points).** Let `ξ_N(w) = exp(2πi w_2/N)`, where
`w_2` is the `a^2`-coordinate. Then `Stab(ξ_N) = Γ ∩ (1 + NL)`. The reason is
that the `a^2`-coordinates of `x`, `ax` and `a^2 x` form a unitriangular
system in the coordinates of `x`. Orbits of different `N` are disjoint and
finite. More generally (referee's Lemma 3′), for `p ∈ {2,3}` every point of
exact order `p^j` has stabilizer `Γ ∩ (1 + p^j L)`: the ideal
`(γ^{-1}-1)L + p^j L` lies in the kernel, and since `p` is inert it equals
some `p^i L`, and exactness of the order forces `i = j`.

**Lemma 4 (p-adic, `p = 2, 3`).**

- Both primes are inert in `L`, so `log : 1 + p^m L_p → p^m L_p` is a
  valuation-preserving isomorphism, with `m = 2` for `p = 2` and `m = 1` for
  `p = 3`.
- The exact certificate in
  `experiments/stw99-lxxxvi-berend-dual-circle-rokhlin-2026-09-16/padic_certificate.py`
  shows that `log a^e` and `log (a+1)^e` are `Z_p`-independent, with `e = 14`
  for `p = 2` and `e = 26` for `p = 3`. It does this by computing a `2×2`
  minor of valuation `≤ 4` modulo `p^40`.
- Flatness gives injectivity of `log` on `Z_p ⊗ Γ'` for `Γ' = Γ ∩ (1 + p^m L)`.
  Let `p^c` be the saturation index of its image. Then
  `Γ ∩ (1 + p^j L) ⊆ Γ^p` for all `j ≥ max(m, c+1)`.

**Assembly.**

1. *Choice of `p` and `s`.* Put `H = S^⊥`. If `S` is infinite, or if
   `p | |S|`, then `H Γ^p ≠ Γ`. So there is `s ≠ 1` in `S ∩ (Γ^p)^⊥`.
2. *A finite orbit in the ideal.* Topological freeness and ideal intersection
   (BPP1, from the required node) give `I ∩ C(X) = C_0(U)` with `U ≠ ∅` open
   and invariant. Points of exact order `p^j` are dense for large `j`, so `U`
   contains one with `j ≥ j_0`. Its orbit `Y` is finite, lies in `U`, and by
   Lemmas 3′ and 4 has `Stab(Y) ⊆ Γ^p`. The Berend invariant-set property is
   not needed.
3. *The quotient.* Restriction `q_Y` maps `I` onto `B_Y`, since a function in
   `C_0(U)` equal to `1` on `Y` lies in `I`.
4. *Conclusion.* Since `s ∈ Stab(Y)^⊥`, Lemmas 2 and 1 give infinite Rokhlin
   dimension.

For `I = A` the ideal-intersection input is not needed either. For `A ⊗ D`
(`D` unital) use `q_Y ⊗ id`; `A ⊗ D` is unital, hence σ-unital.
