---
rg: 2
id: biorderable-v-subgroup-not-in-f-via-golden-ratio-group
kind: route
title: If F_τ embeds in V, it answers the reposed Problem 2.15 negatively
target: biorderable-subgroup-of-v-without-free-subgroups-not-in-f
requires:
  - cleary-golden-ratio-group-embeds-in-thompson-v
  - cleary-golden-ratio-group-does-not-embed-in-thompson-f
  - pl-plus-interval-has-no-non-abelian-free-subgroups
---

## Why sufficient

Let `F_τ = F([0,1]; Z[τ], ⟨τ⟩)` be Cleary's golden-ratio group, and suppose `F_τ` is
isomorphic to a subgroup `H` of `V` (`cleary-golden-ratio-group-embeds-in-thompson-v`).
We check that `H` is a witness for the target.

1. **`H` is not a subgroup of `F`.** This is
   `cleary-golden-ratio-group-does-not-embed-in-thompson-f`, since `H ≅ F_τ`.
2. **`H` is bi-orderable.** Every subgroup of `PL_+([0,1])` is bi-orderable, and here is
   the argument.
   - For `f ≠ 1`, let `p_f = inf supp(f)`. Then `f(p_f) = p_f`, and `f'(p_f+) ≠ 1`, since
     otherwise `f` would be the identity on some `[p_f, p_f + ε)`.
   - Put `P = {f ≠ 1 : f'(p_f+) > 1}`. Then `G = P ⊔ P^{-1} ⊔ {1}`, because
     `p_{f^{-1}} = p_f` and `(f^{-1})'(p_f+) = f'(p_f+)^{-1}`.
   - *`P` is closed under products.* Let `f, g` be in `P`. If `p_f < p_g`, then `fg`
     agrees with `f` near `p_f` from the right and is the identity left of `p_f`, so
     `p_{fg} = p_f` with slope `f'(p_f+) > 1`. The case `p_g < p_f` is symmetric. If
     `p_f = p_g = p`, then `fg` is the identity left of `p` and
     `(fg)'(p+) = f'(p+)·g'(p+) > 1`, so `fg ≠ 1` and `p_{fg} = p`.
   - *`P` is invariant under conjugation.* For any `h`, `p_{hfh^{-1}} = h(p_f)`, and the
     chain rule gives `(hfh^{-1})'(h(p_f)+) = h'(p_f+)·f'(p_f+)·(h^{-1})'(h(p_f)+)`,
     which equals `f'(p_f+)`.
   - So `P` is the positive cone of a bi-invariant order on `PL_+([0,1])`, and `F_τ` is a
     subgroup of it. This is the argument behind the established
     `thompson-f-is-bi-orderable`, applied without restricting slopes.
3. **`H` has no non-abelian free subgroup.** `F_τ` is a subgroup of `PL_+([0,1])`, which
   has none (`pl-plus-interval-has-no-non-abelian-free-subgroups`: Brin–Squier, Invent.
   Math. 79 (1985), in Monod's piecewise projective form), and `H ≅ F_τ`.

So `H` is a bi-orderable subgroup of `V` with no non-abelian free subgroup that is
isomorphic to no subgroup of `F`, which is the target claim.

## Scope

- The implication is complete given its three prerequisites. Step 2 is proved in full
  above. (Referee 2026-09-16: step 3 originally leaned on the `F`-only import
  `thompson-f-no-free-subgroups-citation` without listing it; it now requires the
  `PL_+([0,1])` claim explicitly.)
- The prerequisite `cleary-golden-ratio-group-embeds-in-thompson-v` is open, and
  Hyde–Skipper–Zaremsky expect it to be false. This route records the sharpest surviving
  candidate after `biorderable-v-subgroup-not-in-f-via-wreath-z-by-z2` was killed by
  `wreath-z-by-z2-does-not-embed-in-thompson-v`.
