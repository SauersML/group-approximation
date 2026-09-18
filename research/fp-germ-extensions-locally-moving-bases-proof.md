---
rg: 2
id: fp-germ-extensions-locally-moving-bases-proof
kind: route
title: Run the V proof with the base axiomatized; finite generation realizes base arrows, finitely presented isotropy makes the groupoid vertex group finitely presented, and local moving kills the germ kernel
target: fp-germ-extensions-of-locally-moving-bases-have-fp-germ-groups
requires:
  - fp-almost-v-groups-have-fp-germ-groups
---

Follow `fp-almost-v-groups-fp-germ-groups-proof` step by step with `B` in place of `V`. Fix
`p`, a finite generating set `Y` of `B` (B1), and a finite presentation `E = <Y ∪ Z | R>`.
Put `Ω = E·p`, `St = Stab_E(p)`, `F = ⋃_{z in Z}(sing(z) ∪ z(sing z))`.

1. **Finitely many base orbits.** Letters of `Y` preserve `B`-orbits. A letter `z^±` at a
   non-singular point agrees near it with an element of `B`, so it also preserves the
   `B`-orbit. Since `sing(z^-1) = z(sing z)`, orbit changes happen only at points of `F`. So
   `Ω ⊆ B·({p} ∪ F)`.
2. **The groupoid.** `G_B` is the germ groupoid of `B` on `Ω`: arrows `(b)_x : x -> b(x)`. Its
   components are the finitely many `B`-orbits in `Ω`, and its isotropy at `x` is `(B)_x`.
   Adjoin one free arrow `σ_(z,x)` for each `z in Z` and `x in sing(z) ∩ Ω`, to get `Π`,
   which is connected. Its vertex group `Π_p` is the free product of one conjugate of `(B)_x`
   per component with a free group of finite rank. By (B2) it is finitely presented.
3. **Words to arrows.** Letters of `Y` go to their `G_B` germs. `z` at a non-singular `x` goes
   to the `G_B` germ of any element of `B` agreeing with it near `x`, which is well defined. At
   `x in sing(z)` it goes to `σ_(z,x)`. Relators read from points where they apply no letter
   at a singular point map to their actual germ, which is trivial. The exceptional starting
   points are finite in number for each relator, because the prefix before each letter acts as
   a permutation of `X` and singular sets are finite. This gives `Φ : St -> Q_R = Π_p/<<W_R>>`
   with `W_R` finite. `Φ` is onto: a `G_B` arrow `(b)_x` is realized by a `Y`-word for `b`
   (B1), and `σ_(z,x)` by `z` at `x`.
4. **Back to germs.** `σ_(z,x) ↦ (z)_x` gives `Ψ : Q_R -> (E)_p` with `Ψ∘Φ` the germ map.
5. **The germ kernel dies (B3).** Let `l in St` be the identity on an open `U ∋ p`, with word
   `w`. Let `B_w` be the finite set of points from which `w` applies a letter at one of its
   singular points. By (B3) choose `c in B` supported in `U` with `p' = c(p) ∉ B_w`. Then `c`
   commutes with `l`: both preserve `U` and its complement, `l` is trivial on `U`, and `c` is
   trivial off `U`. Read `c^-1 w c` from `p`: its image in `Π` is `γ^-1 · λ · γ`, where `γ` is
   the image of the path of `c` from `p` to `p'` (whatever arrows it uses), and `λ` is the
   image of `w` read from `p'`. Since `p' ∉ B_w`, `λ` consists of `G_B` arrows and equals the
   germ of `l` at `p'`. That germ is trivial because `p' in U`. So `Φ(l) = 1`.
6. **Conclusion.** As in the `V` case, `Φ` factors as `Φ̄` through the germ map, and `Ψ∘Φ̄` and
   `Φ̄∘Ψ` are identities (the second because `Φ` is onto). So `(E)_p ≅ Q_R` is finitely
   presented. `∎`

**Remark.** Step 5 does not need `c` to be written in `Y`. This is also what makes the argument
base-independent: only local moving is used, not the tail-class structure of `V`-orbits.
