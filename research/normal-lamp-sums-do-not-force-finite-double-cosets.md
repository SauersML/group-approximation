---
rg: 2
id: normal-lamp-sums-do-not-force-finite-double-cosets
kind: claim
title: A finitely presented group can normalize an infinite direct sum of conjugates of a finite subgroup whose normalizer is normal of infinite index, but not once the normalizer splits off that subgroup as a direct factor
distinct_from:
  tits-independence-amalgams-force-self-product-edge-groups: that proves edge groups with the edge-product property contain arbitrarily large direct powers and leaves open whether a finitely presented vertex group can carry the normal sum D_A over infinitely many cosets; this refutes the abstract Cornulier-style implication "normal lamp sum in a finitely presented group forces finitely many double cosets" and proves the implication once C = V x W with W_x <= V and C normal and finitely generated.
  abstract-btb-pairs-fp-and-relatively-simple: that characterizes finite presentability of abstract twisted Brin--Thompson groups by the [A_2] condition on the action; this is about vertex groups of amalgams and shows no [A_2]-type finiteness condition is forced by a normal lamp sum alone.
---

**ESTABLISHED (unreviewed).** Proof: `normal-lamp-sums-do-not-force-finite-double-cosets-proof`.

**Question.** Let `A` be a group, `W ≤ A`, `C = N_A(W)`, and `W_x = aWa^{-1}` for
`x = aC ∈ A/C`. Suppose the `W_x` generate their direct sum `D_A = ⊕_{x ∈ A/C} W_x`.
`D_A` is then automatically normal. For a wreath product `W ≀_X Q`, Cornulier's
theorem says finite presentability forces finitely many orbits on `X²`, which here
means `|C\A/C| < ∞`. Does finite presentability of `A` force `|C\A/C| < ∞` in
general? If yes, vertex groups of a Tits-(P) amalgam would be twisted
Brin--Thompson-like and the (P) route would collapse into known [A_2] constraints.

**Theorem.**

1. **(Counterexample.)** Let `R = F_p[t, t^{-1}, (t-1)^{-1}]`, `E = A_4(R)` Abels'
   group, `δ = diag(t,1,1,1)` and `A = E ⋊ ⟨δ⟩`. Let `W = {I + λE_{14} : λ ∈ F_p} ≅ Z/p`.
   Then `A` is finitely presented, `C = N_A(W) = E` is normal, finitely presented and
   of infinite index, `A/C ≅ Z`, the conjugates `W_{δ^c C} = I + F_p t^c E_{14}`
   generate their direct sum `D_A = I + F_p[t^{±1}]E_{14}`, and `D_A` is central in
   `C` and normal in `A`. So `|C\A/C| = ∞`. The abstract implication is false, even
   with `W` finite, `C` finitely presented and `D_A ≤ Z(C)`.
2. **(Where it fails, and the repair.)** Say `(A, C, W)` has **split edge data** if
   `C = V × W` for some `V` and `W_x ≤ V` for every `x ∈ A/C` with `x ≠ C` (this is
   item 2 of `tits-independence-amalgams-force-self-product-edge-groups`). If `C` is
   normal and finitely generated, the data are split, and `W` has a nontrivial finite
   quotient `S`, then `[A:C] ≤ |Hom(C,S)| < ∞`.
3. The example in item 1 is not split for any `V`: there `1 ≠ W ≤ [C,C]`, while an
   abelian direct factor `W` of `C = V × W` meets `[C,C] = [V,V] × 1` trivially.

**What this settles for `boone-higman-conjecture`.** The Tits-(P) route is not
killed by a Cornulier-type finiteness theorem for normal lamp sums: finitely
presented solvable groups already carry infinite normal lamp sums with infinite
normalizer index. It is also not freed by them: the counterexample mechanism, a
central lamp sum produced as commutators, is incompatible with the edge-product
splitting, and item 2 shows split data with normal finitely generated `C` and
`W` having a nontrivial finite quotient force finite index. The remaining Tits-relevant form is the open question below, with `C` not normal.

**Open.** Let `A` be finitely presented, `C ≤ A` finitely generated, with split edge
data. Must `|C\A/C|` be finite? A positive answer puts every Tits-(P) vertex group
into the finite-double-coset regime of Cornulier and FFWZ.
