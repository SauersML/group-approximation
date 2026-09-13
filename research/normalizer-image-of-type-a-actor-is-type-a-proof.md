---
rg: 2
id: normalizer-image-of-type-a-actor-is-type-a-proof
kind: route
title: Check faithfulness, finite presentation, pair orbits and stabilizers of the product with a normalizing group
target: normalizer-image-of-type-a-actor-is-type-a
requires: []
---

Put `Λ = ΓQ <= Sym(S)`. Since `Q` normalizes `Γ`, `Λ` is a subgroup, `Γ` is
normal in it, and `Λ/Γ ≅ Q/(Q ∩ Γ)`.

1. **Faithful.** `Λ` is a group of permutations of `S`.
2. **Finitely presented.** An extension of the finitely presented group `Γ` by
   the finitely presented group `Λ/Γ` is finitely presented (P. Hall). Take the
   generators of both, the relators of `Γ`, lifted relators of `Λ/Γ` corrected by
   words in `Γ`, and the finitely many conjugation relations of the lifted
   generators on the generators of `Γ`.
3. **Finitely many pair orbits.** Every `Λ`-orbit on two-element subsets is a
   union of `Γ`-orbits, and there are finitely many of those.
4. **Finitely generated stabilizers.** Fix `s in S`, and let
   `π : Stab_Λ(s) -> Λ/Γ` be the restriction of the quotient map.
   - *Kernel.* `ker π = Stab_Γ(s)`, which is finitely generated.
   - *Image.* It is the stabilizer of the orbit `Γs` in the action of `Λ/Γ` on the
     set of `Γ`-orbits, which is well defined because `Γ` is normal. If `λ = γq`
     fixes `s`, then `q s = γ^-1 s` lies in `Γs`. Conversely, if `λ s = γ' s`, then
     `γ'^-1 λ` fixes `s` and has the same image.
   - *The image is finitely generated.* When `|S| >= 2`, finitely many orbits on
     pairs force finitely many `Γ`-orbits on points. So the image has finite
     index in the finitely presented group `Λ/Γ`.
   - An extension of a finitely generated group by a finitely generated group is
     finitely generated.

So `Λ` acts on `S` with type (A). For the complexity consequence, `Q` is generated
by finitely many elements of `Λ`. Each is a fixed word in the generators of `Λ`,
so a word of length `l` over `Q` rewrites to one of length at most `Cl` over `Λ`
with the same value. `∎`
