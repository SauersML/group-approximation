---
rg: 2
id: two-one-bump-pl-maps-unequal-supports-ea-or-contain-f-proof
kind: route
title: "Proof: case analysis of two one-bump PL maps by the position of their supports"
target: two-one-bump-pl-maps-unequal-supports-ea-or-contain-f
requires:
  - kim-koberda-lodha-2-prechain-powers-generate-f
  - brin-plo-i-one-sided-approach-gives-a-copy-of-f
---

Write `A = (a,b)`, `B = (c,d)`, `G = ⟨f, g⟩`. Two different open intervals are either
disjoint, or meet with neither containing the other, or properly nested; properly
nested intervals share at most one endpoint, and `B ⊊ A` shares no endpoint iff
`B̄ ⊂ A`. So the cases below are exhaustive. A one-bump map moves all points of its
support in one direction (`t ↦ f(t) − t` is continuous with no zero on the support),
and every nontrivial element of `PL_o(I)` has infinite order.

**Disjoint supports.** `f` and `g` commute. If `f^p g^q = 1`, restricting to `A` gives
`f^p = 1`, so `p = 0`, and then `q = 0`. So `G ≅ ℤ²`.

**Overlapping supports (3a).** After renaming, `a < c < b < d`. By
`kim-koberda-lodha-2-prechain-powers-generate-f`, `⟨f^{εN}, g^{δN}⟩ ≅ F` for suitable
signs and large `N`; this is a subgroup of `G`.

**Nested, one shared endpoint (3b).** Say `B ⊊ A`. The support of `G` is `A ∪ B = A`,
so `A` is an orbital of `G`. The only orbital of `g` is `B`, it lies in `A`, and it has
exactly one endpoint in common with `A`. So `g` approaches one end of `A` but not the
other, and `G` contains `F` by `brin-plo-i-one-sided-approach-gives-a-copy-of-f`.

**Nested, no shared endpoint.** Say `B̄ ⊂ A`, so `c, d ∈ A` are moved by `f`, all in the
same direction.

- *(3c) Some translate meets `B`.* Let `n ≠ 0` with `f^n(B) ∩ B ≠ ∅`. Then
  `f^n(B) = (f^n(c), f^n(d))` with `f^n(c) − c` and `f^n(d) − d` nonzero of the same
  sign, so neither of `B`, `f^n(B)` contains the other, and they meet. The maps `g` and
  `g' = f^n g f^{-n}` are one-bump with supports `B` and `f^n(B)` in the overlapping
  position, so `⟨g, g'⟩ ≤ G` contains `F` by the overlapping case.
- *(2) All translates disjoint.* If `f^n(B) ∩ f^m(B) ≠ ∅` then `f^{n−m}(B) ∩ B ≠ ∅`, so
  the translates are pairwise disjoint. Put `g_n = f^n g f^{-n}`, one-bump with support
  `f^n(B)`. The `g_n` commute. A product `∏ g_n^{k_n}` restricted to `f^m(B)` is
  `g_m^{k_m}`, so it is trivial only if all `k_n = 0`: `N := ⟨g_n : n ∈ ℤ⟩ ≅ ⊕_ℤ ℤ`, with
  `f g_n f^{-1} = g_{n+1}`. The point `d` lies in no translate: `d ∉ B`, and `d ∈ f^n(B)`
  for `n ≠ 0` would give `f^n(c) < d`, i.e. `f^n(B) ∩ B ≠ ∅`. So `N` fixes `d`, while
  `f^m` moves `d` for `m ≠ 0`; hence `N ∩ ⟨f⟩ = 1`. Since `G = N⟨f⟩` and `N` is normal in
  `G`, `G = N ⋊ ⟨f⟩` with `f` acting by the shift on `⊕_ℤ ℤ`, i.e. `G ≅ ℤ ≀ ℤ`.

**Exclusivity.** `ℤ²` and `ℤ ≀ ℤ` are elementary amenable, so they contain no copy of
`F`; and the geometric conditions in 1, 2, 3 are mutually exclusive.

**Model test.** Standard `F` has generators `x_0` (one bump on `(0,1)`) and `x_1` (one
bump on `(1/2, 1)`): case 3b, and indeed they generate `F`. Taking instead `g` a bump
on `(1/8, 1/4)` and `f = x_0`, whose inverse maps `(1/8,1/4)` into `(1/16, 1/8)` in the
standard action, the translates of `(1/8, 1/4)` under powers of `x_0` are pairwise
disjoint, and the claim gives `ℤ ≀ ℤ`.
