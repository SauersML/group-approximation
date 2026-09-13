---
rg: 2
id: f-free-plo-i-groups-have-equal-end-germ-kernels
kind: claim
title: "In a subgroup of PL_o(I) with no copy of F, on every orbital of every subgroup an element is trivial near one end iff it is trivial near the other"
---

**Statement.** Let `H ≤ PL_o(I)` have no subgroup isomorphic to Thompson's group `F`.
Let `D ≤ H` and let `A = (a,b)` be an orbital of `D`, with the slope germs `χ_a^D`,
`χ_b^D` and the germ-trivial kernel `K_A(D)` of
`plo-i-group-is-ea-iff-its-orbital-germ-kernels-are`. Then

`ker χ_a^D = ker χ_b^D = K_A(D)`.

Consequently:

- `D_A / K_A(D)_A` embeds in `(ℝ_{>0}, ·)` through `χ_a^D` alone, and
  `χ_b^D = ψ ∘ χ_a^D` for a unique homomorphism `ψ: χ_a^D(D) → ℝ_{>0}`;
- if `D` is finitely generated, `D_A / K_A(D)_A ≅ ℤ^r` with `r ≥ 1`.

In particular every pair `(D_i, A_i)` in the descent of
`plo-i-group-is-ea-iff-its-orbital-germ-kernels-are` (5) has this property when `H`
is `F`-free: the slope germs at the two ends of each orbital are synchronized.

**Model tests.** Standard `F = ⟨x_0, x_1⟩` on `(0,1)`: `x_1` is the identity near `0`
and has slope `≠ 1` near `1`, so the kernels differ, consistent with `F` containing
`F`. `ℤ ≀ ℤ = ⟨t, g⟩` (`t` one bump on `(0,1)`, `g` a bump on `J` with `t^n(J)` pairwise
disjoint): an element `t^k w`, with `w` in the normal closure of `g`, has slope `λ^k`
at both `0` and `1`, where `λ = χ_0(t)`, so the kernels agree.

Proof route: `f-free-plo-i-groups-have-equal-end-germ-kernels-proof`.
