---
rg: 2
id: sp4-projective-models-cocycles-to-one-round-strictly-proof
kind: route
title: Sp_4(Z) has finitely generated H_2 and finitely many realized classes, so the general rounding theorem applies
target: sp4-projective-models-with-cocycles-to-one-round-strictly
requires:
  - finite-fd-multiplier-projective-models-round-strictly
  - sp4-fd-projective-multiplier-is-finite
---

The general theorem `finite-fd-multiplier-projective-models-round-strictly` needs three
inputs at `Γ = Sp_4(Z)`.

1. **`Γ` is finitely generated.** Bender's presentation has 2 generators and 8 relations. It is
   quoted, source-verified, in Step 0 of `sp4-fd-projective-multiplier-finiteness-proof`, the
   route of `sp4-fd-projective-multiplier-is-finite`.
2. **`H_2(Γ;Z)` is finitely generated.** The same Step 0 gives `H_2(Γ;Z) = Z⟨h⟩ + F` with `F`
   finite (display (FP2) there), by Hopf's formula applied to the finite presentation.
3. **The realized set `R` is finite.** `sp4-fd-projective-multiplier-is-finite` states this:
   `R` is a finite subgroup of `H^2(Γ;T)` with `|R| <= 2t^2`, `t = |F|` (display (FM1)).

With these inputs the general theorem gives the conclusion verbatim.
