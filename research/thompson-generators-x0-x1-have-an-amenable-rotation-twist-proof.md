---
rg: 2
id: thompson-generators-x0-x1-have-an-amenable-rotation-twist-proof
kind: route
title: The half-rotation twist of x_0 is an order-3 arc permutation and x_1 lives on one of its arcs, so the group is a wreath product of Z with Z/3
target: thompson-generators-x0-x1-have-an-amenable-rotation-twist
requires: []
---

Left actions throughout. On `[0,1]`: `x_0(s) = s/2` on `[0,1/2]`, `s − 1/4` on `[1/2,3/4]`, `2s − 1` on
`[3/4,1]`; `x_1(s) = s` on `[0,1/2]` and `x_1(s) = 1/2 + x_0(2s − 1)/2` on `[1/2,1]`. So `supp x_1 = (1/2, 1)`.

**Step 1 (`A = x_0ρ_{1/2}` permutes three arcs).** `A(t) = x_0(t + 1/2 mod 1)`.
- For `t ∈ [1/2, 1]`: `s = t − 1/2 ∈ [0, 1/2]`, so `A(t) = t/2 − 1/4`. This maps `I_0 = [1/2, 1]` affinely
  onto `[0, 1/4] = I_1`.
- For `t ∈ [0, 1/4]`: `s = t + 1/2 ∈ [1/2, 3/4]`, so `A(t) = t + 1/4`. This maps `I_1` onto `[1/4, 1/2] = I_2`.
- For `t ∈ [1/4, 1/2]`: `s ∈ [3/4, 1]`, so `A(t) = 2t`. This maps `I_2` onto `[1/2, 1] = I_0`.

`A³` maps each arc to itself by a composite of affine maps fixing both endpoints, so it is the identity on
each arc. And `A ≠ 1`, `A³ = 1`, so `A` has order 3. For example on `I_1`:
`t ↦ t + 1/4 ↦ 2t + 1/2 ↦ t + 1/4 − 1/4 = t`.

**Step 2 (`N ≅ Z³`).** `B = x_1` has infinite order and `supp B = (1/2, 1) = int I_0`. Then
`supp ABA^{-1} = A(int I_0) = int I_1` and `supp A²BA^{-2} = int I_2`. Homeomorphisms with disjoint supports
commute, and a product `B^{k_0}(ABA^{-1})^{k_1}(A²BA^{-2})^{k_2}` restricts to `A^jB^{k_j}A^{-j}` on `I_j`, so it
is trivial only if all `k_j = 0`. Hence `N ≅ Z³`.

**Step 3 (`H = N ⋊ ⟨A⟩`).** Conjugation by `A` permutes the three generators of `N` cyclically, because
`A³ = 1`. Conjugation by `B` fixes `B` and fixes the other two generators, since their supports are disjoint
from that of `B`. So `N` is normal in `H = ⟨A, B⟩`, and `H = N⟨A⟩`. Every element of `N` fixes `0, 1/4, 1/2`,
while `A` and `A²` move `0` (to `1/4` and `1/2`), so `N ∩ ⟨A⟩ = 1`. Therefore `H = N ⋊ Z/3`, with `Z/3`
permuting the three `Z` factors regularly: `H ≅ Z ≀ Z/3`. It contains `Z³` with index 3, so it is amenable.

**Step 4 (the orbit in `T/R_D`).** `A ∈ x_0R_D` and `B ∈ x_1R_D`. So `A·R_D = x_0R_D` and `B·R_D = x_1R_D`,
and `R_D`, `x_0R_D`, `x_1R_D` lie in the `H`-orbit of the base point. By the reformulation in
`thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive` (twists `θ_{x_0} = 1/2`, `θ_{x_1} = 0`), the set
`{x_0, x_1}` is not a witness. ∎

**Mechanism.** Steps 2 and 3 use only three facts: `c = A` has finite order `m` and permutes a partition into
arcs; `U = {B}` is supported inside one arc `I`; and the arcs `c^jI` (`0 ≤ j < m`) are distinct. Under those
hypotheses the same argument gives `⟨c, U⟩ = (∏_j c^j⟨U⟩c^{-j}) ⋊ ⟨c⟩ ≅ ⟨U⟩ ≀ Z/m`.
