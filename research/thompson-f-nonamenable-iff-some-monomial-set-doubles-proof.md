---
rg: 2
id: thompson-f-nonamenable-iff-some-monomial-set-doubles-proof
kind: route
title: Følner sets translated into the positive monoid, and iterated expansion of a homogeneous set
target: thompson-f-nonamenable-iff-some-monomial-set-doubles
requires: []
artifacts:
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13.md
---

Standard facts used:
- the Følner criterion for groups;
- amenability passes to subgroups, extensions and directed unions;
- the Cannon–Floyd–Parry normal form: every `g ∈ F` is `p q^-1` with `p, q ∈ M`;
- `K[F]` has no zero divisors (`thompson-f-amenable-iff-group-ring-is-ore`, step 2).

`deg` is the homomorphism `F -> Z` with `deg x_i = 1`.

**Step 0 (common right multiples).** For `p, q ∈ M` the element `q^-1 p` is `u v^-1` with
`u, v ∈ M`, so `p v = q u`. By induction, finitely many `q_1, ..., q_n ∈ M` have a common right
multiple `r = q_i t_i` with `t_i ∈ M`. Hence for `g_i = p_i q_i^-1` the element `g_i r = p_i t_i`
lies in `M`. This is the survey's Lemma `gig`.

**Item 1.** Let `F` be amenable and `S ⊆ M` finite. By Følner there is a finite nonempty
`Z ⊂ F` with `|s Z \ Z| < |Z| / |S|` for every `s ∈ S`. By Step 0 there is `r` with `Z r ⊆ M`.
Put `Y = Z r`. Right multiplication is a bijection, so `|s Y \ Y| = |s Z \ Z|`. Since
`S Y ⊆ Y ∪ ⋃_s (s Y \ Y)`, we get `|S Y| <= |Y| + Σ_s |s Y \ Y| < 2|Y|`.

**Item 2.**
- *A non-amenable finitely generated subgroup of degree zero.* Let `F` be non-amenable and
  `N = ker deg`. Since `F / N ≅ Z` is amenable, `N` is non-amenable. Being the directed union
  of its finitely generated subgroups, `N` has a finitely generated non-amenable subgroup
  `⟨k_1, ..., k_n⟩`.
- *Failure of the Følner condition.* By Følner there is `ε > 0` such that every finite
  nonempty `Z ⊂ F` has some `i` with `|k_i Z \ Z| >= ε |Z|`.
- *A common denominator.* Write `k_i = p_i q_i^-1` with `p_i, q_i ∈ M`. Here `deg p_i = deg q_i`,
  because `deg k_i = 0`. By Step 0 take `r ∈ M` and `t_i ∈ M` with `r = q_i t_i`, and put
  `a_i = p_i t_i`. Then `k_i = a_i r^-1`, and every `a_i` has degree `deg r`.
  So `T = {r, a_1, ..., a_n}` is homogeneous of degree `deg r`.
- *One step of expansion.* For finite nonempty `Y ⊆ M`, put `Z = r Y`, so `|Z| = |Y|`, and
  choose `i` for this `Z`. Then
  `|T Y| >= |r Y ∪ a_i Y| = |Z ∪ k_i Z| = |Z| + |k_i Z \ Z| >= (1+ε)|Y|`.
- *Iteration.* `T^j Y = T(T^(j-1) Y)` and `T^(j-1) Y ⊆ M` is finite, so induction gives
  `|T^j Y| >= (1+ε)^j |Y|`. Choose `j` with `(1+ε)^j >= 2`.
- *Enlarging to a monomial set.* `T^j` is a finite set of normal forms of one degree
  `d = j deg r`. It is contained in `S_(m+1,m+d+1)` once `m` is at least its largest letter:
  then `i_t <= m <= m + t - 1`. Enlarging `S` only enlarges `S Y`, so `S_(m+1,m+d+1)` is doubling.

**Item 3.** Let `|S Y| < 2|Y|` and `a, b ∈ K[S]` nonzero. The `K`-linear map
`K[Y] × K[Y] -> K[S Y]`, `(u, v) -> a u - b v`, has domain dimension `2|Y|` greater than the
target dimension `|S Y|`. So it has a nonzero kernel element `(u, v)`. If `u = 0`, then
`b v = 0`, so `v = 0` because `K[F]` has no zero divisors; this is impossible. Symmetrically
`v ≠ 0`. So `a u = b v` with `u, v ≠ 0`.

**Consequence.** Items 1 and 3 show that amenability makes the method solve every `P_(d,m)`.
Item 2 shows that non-amenability makes it fail at some `(d,m)`, since the set is doubling.
Both directions are sharp because the method uses nothing about `a, b` beyond their supports.
