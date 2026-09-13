---
rg: 2
id: f-free-plo-i-groups-have-equal-end-germ-kernels-proof
kind: route
title: "Proof: Brin's criterion synchronizes the end germs of F-free subgroups of PL_o(I)"
target: f-free-plo-i-groups-have-equal-end-germ-kernels
requires:
  - brin-plo-i-one-sided-approach-gives-a-copy-of-f
---

Let `D ≤ H`, so `D` has no subgroup isomorphic to `F`, and let `A = (a,b)` be an
orbital of `D`.

**Approaching an end is a nontrivial germ.** Let `h ∈ D`. As in
`plo-i-group-is-ea-iff-its-orbital-germ-kernels-are` (1), `h` fixes `a` and
`h(x) = a + λ(x − a)` on some `[a, a+ε]`, with `λ = χ_a^D(h)`.

- If `λ ≠ 1`, `h` has no fixed point in `(a, a+ε]`. The component of `supp(h)`
  containing `(a, a+ε)` is an orbital of `h` with endpoint `a`, and it lies in `A`
  because `supp(h) ⊆ supp(D)` and `A` is a component of `supp(D)`. So `h` approaches
  `a` in `A`, in the sense of Brin (`brin-plo-i-one-sided-approach-gives-a-copy-of-f`).
- If `λ = 1`, `h` is the identity on `[a, a+ε]`, so no orbital of `h` has endpoint
  `a`, and `h` does not approach `a` in `A`.

The same holds at `b` with `χ_b^D`.

**Balance.** If some `h ∈ D` had `χ_a^D(h) ≠ 1 = χ_b^D(h)` or the reverse, then `h`
would approach exactly one end of the orbital `(a,b)` of `D`, and Brin's Theorem 1
would give a subgroup of `D` isomorphic to `F`, a contradiction. So
`χ_a^D(h) = 1 ⟺ χ_b^D(h) = 1`, i.e. `ker χ_a^D = ker χ_b^D`, and both equal
`K_A(D) = ker χ_a^D ∩ ker χ_b^D`.

**Consequences.** `χ_a^D` induces an injection `D_A / K_A(D)_A → ℝ_{>0}`, and
`ψ(χ_a^D(h)) := χ_b^D(h)` is well defined because `χ_a^D(h) = χ_a^D(h')` implies
`h^{-1}h' ∈ ker χ_a^D = ker χ_b^D`; it is a homomorphism because `χ_b^D` is. If `D` is
finitely generated, the image of `χ_a^D` is a finitely generated subgroup of the
torsion-free abelian group `ℝ_{>0}`, hence `≅ ℤ^r`. If `r = 0`, every generator is the
identity near `a`, so `supp(D)` does not meet some `(a, a+ε)`, contradicting that `A`
is an orbital of `D`; so `r ≥ 1`.
