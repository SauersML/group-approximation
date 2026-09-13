---
rg: 2
id: radu-edge-coset-action-is-sofic
kind: claim
title: The action of Radu's arithmetic quotient on the oriented x/z-edges of the Cayley graph of PGL_2(Z) is a sofic set action
distinct_from:
  coordinate-action-not-sofic: that refutes soficity of the Kun-Thom coset action through property (T) of the stabilizer; here the stabilizer C_chi is a free product of four involutions, a-T-menable, and no nonsoficity mechanism is known
  radu-metabelian-quotient-embeds-in-edge-lamp-wreath: that proves soficity of this action implies soficity of G_2; this asks for the action itself
  radu-square-lamp-forces-reflections-in-finite-actions: that excludes genuine finite actions as models of this coset action; this asks for approximate ones
  dyadic-bruhat-tits-vertex-action-is-sofic: that is the action of PSL_2(Z[1/2]) on its dyadic tree, with a single inverted prime and stabilizer PSL_2(Z); this is the action of a quaternionic lattice with two inverted primes on a double cover of the framed vertices of its second tree, with stabilizer a free product of involutions
artifacts:
  - research/artifacts/radu-edge-lamp-host-and-square-firewall-2026-09-13.md
---

**OPEN.** Let `Q` be the cocompact arithmetic lattice of `radu-horizontal-quotient-is-arithmetic-lattice`,
and `C_χ = <a, b, cac, cbc> ⊂ C = <a,b,c>`, the stabilizer of the oriented edge `o → xo` of
`Y = Cay(PGL_2(Z); x,y,z)`. The claim is that

```text
Q ↷ Q/C_χ   (the oriented {x,z}-edges of Y)
```

is sofic in the sense of Gao–Kunnawalkam Elayavalli–Patchell, Definition 2.1(5). There must be almost
actions `φ` of `Q` on finite sets `A`, and on most points `s` injective colourings `π_s` of a finite
window `E ⊂ Q/C_χ` with `π_(φ(g)s)(x) = π_s(g^(−1)x)`. By `radu-metabelian-quotient-embeds-in-edge-lamp-wreath`
this implies that `G_2 = Γ_R/[Λ_v, Λ_v]` is sofic.

**Shape of a model.** A colouring `f(s) = π_s(C_χ)` is almost invariant under `a, b, cac, cbc` and
separates `s` from `φ(g)s` for the eight elements `g` of `D_4 = <x, c>`. Equivalently, the almost
action carries an almost `C_χ`-invariant partition that each reflection `x, z, c, xzc` moves off
itself on most points.

## Attempts

* **Genuine finite actions: dead.** `radu-square-lamp-forces-reflections-in-finite-actions`, item 3.
  An exactly `C_χ`-invariant colouring is fixed by some reflection of the square. The reason is Radu's
  finite residual, and no congruence input is used.
* **Almost actions close to genuine ones: dead if `Q` has spectral gap and stability.**
  - Suppose `C_χ` has a uniform spectral gap `κ` on all finite `Q`-sets. This would follow from the
    congruence subgroup property for `Q` and property τ for the `{𝔮}`-arithmetic lattice `C`
    (Clozel), neither checked here.
  - Then an `η`-invariant colouring of a genuine action is `O(η/κ^2)`-close to an invariant one, and
    the previous bullet applies.
  - Almost actions within `o(1)` Hamming distance of genuine actions are excluded in the same way, as
    in `codense-tau-coset-soficity-forces-permutation-instability`.
  - So a model must be an almost action of `Q` that is far from every genuine action. It exists only
    if `Q` is not flexibly permutation-stable.
* **Local meaning (verified).** `C` fixes the `S_3`-vertex `p` of the second tree, and
  `C_χ = C ∩ Fix_Q(star of p)` (`radu-horizontal-sign-is-local-action-on-second-tree`).
  - So `Q/C_χ` is a double cover of the framed vertices of `T'`, a `𝔮'`-adic structure. Finite
    quotients of `Q` cannot see it, because `𝔮'` is inverted in `Q`.
  - A model has to see the second prime approximately, although no genuine finite action does.
  - A necessary condition: the action of `Q` on the framed vertices of its second tree must itself
    be sofic.
* **Same fork as the dyadic vertex action.**
  - This is one instance of the family "an `S`-arithmetic lattice acting on the Bruhat–Tits tree at an
    inverted prime". Other instances are `dyadic-bruhat-tits-vertex-action-is-sofic` (the live route
    there is random lifts with Bass–Serre separation) and `function-field-rank-one-vertex-action-is-sofic`.
  - The fork has the same shape in each case. A positive answer forces flexible permutation
    instability of the lattice (`psl2-bruhat-tits-action-soficity-forces-p-instability`; here
    `radu-edge-coset-action-not-sofic-via-stability`). Genuine finite models are excluded by
    codensity.
  - What differs here: two primes are inverted; the stabilizer `C_χ ≅ C_2^(*4)` is torsion-generated
    and virtually free; the space is a double cover of framed vertices rather than one colour of
    vertices; and the codensity input is proved from Radu's residual instead of from the congruence
    subgroup property.
  - A random-lift construction that works for the dyadic action should be tested on this one.
