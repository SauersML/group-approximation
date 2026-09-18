---
rg: 2
id: weakly-mixing-fibre-products-are-relatively-weakly-mixing
kind: claim
title: The projection of a product with a weakly mixing action onto the other factor is a relatively weakly mixing extension
distinct_from:
  strict-pair-flip-lifts-are-relatively-weakly-mixing: that shows one family of skew extensions of a Bernoulli base is relatively weakly mixing; this is the direct product case A x C -> C for an arbitrary base C and an arbitrary weakly mixing fibre A.
  relative-furstenberg-zimmer-dichotomy: that imports the dichotomy and the definition of relative weak mixing; this verifies the definition for product extensions with a weakly mixing fibre.
artifacts:
  - research/artifacts/fpbs-weakly-mixing-half-is-fixed-price-2026-09-17.md
---

**ESTABLISHED.** Let G be a countable group, A a weakly mixing p.m.p. action of G on (Z, ζ)
(its reduced Koopman representation has no nonzero finite-dimensional subrepresentation), and C
any p.m.p. action of G on (Y, ν). Let f ∈ L²(Z × Y) satisfy E(f|Y) = 0 and E(|f|²|Y) ∈ L²(Y).
Then for every ε > 0 there is g ∈ G with ‖E(U_g f · f̄ | Y)‖_{L²(Y)} < ε. So A × C → C is
relatively weakly mixing in the sense of Definition 6.1 of Jamneshan
(`relative-furstenberg-zimmer-dichotomy`, item (i)). This reads the definition on every f with
E(|f|²|Y) ∈ L²(Y). That class contains all bounded f and the module L²(X|Y).

The proof is in artifact Section 2 (Lemma 4, using Lemmas 1-3 of Section 1). The function
F(z, z', y) = f(z, y) f̄(z', y) lies in L²_0(Z × Z) ⊗ L²(Y), and ⟨U_g F, F⟩ equals
‖E(U_g f f̄ | Y)‖². The representation κ_0^{A×A} ⊗ κ^C has no finite-dimensional
subrepresentation (partial-trace argument). So its matrix coefficients get arbitrarily small (a
least-norm point in the closed convex hull of Hilbert-Schmidt orbits). No freeness or ergodicity of C
is used.
