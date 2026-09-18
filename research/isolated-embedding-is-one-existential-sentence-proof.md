---
rg: 2
id: isolated-embedding-is-one-existential-sentence-proof
kind: route
title: A solution of the presentation defines a homomorphism, and its kernel misses the discriminating subset, so it is trivial
target: isolated-embedding-is-one-existential-sentence
requires: []
---

Notation and imported definitions as in the target.

**(⇒).** Let `ι: H → S` be injective and put `s_j = ι(x_j)`. Each relator
holds in `H`, so `r_i(s) = ι(r_i(x)) = 1`. Each `f_i ≠ 1` in `H`, since
`F ⊂ H − {1}`, so `f_i(s) = ι(f_i) ≠ 1` by injectivity. Hence `s` witnesses
`Σ_H` in `S`.

**(⇐).** Let `s = (s_1, ..., s_n)` in `S^n` witness `Σ_H`.
- Since `r_i(s) = 1` for all `i`, von Dyck's theorem gives a homomorphism
  `φ: H → S` with `φ(x_j) = s_j`.
- `ker φ` is normal in `H`. For each `i`, `φ(f_i) = f_i(s) ≠ 1`, so
  `f_i ∉ ker φ`. Thus `ker φ ∩ F = ∅`.
- `F` is discriminating: every non-trivial normal subgroup of `H` contains
  an element of `F`. So `ker φ = 1`, and `φ` embeds `H` in `S`.

**Consequence 1.** Immediate from the equivalence applied to each member of
`K`.

**Consequence 2.** Suppose `H` embeds in no member of `K`. By Consequence 1,
`¬Σ_H` holds in every member of `K`. But `Σ_H` holds in `H`, witnessed by the
generators `x`, by (⇒) applied to the identity of `H`. So `H` fails a
universal sentence true in all of `K`. Conversely, if `H ≤ S ∈ K` and a
universal sentence `∀ y φ(y)` with `φ` quantifier-free holds in `S`, it holds
for all tuples from `H`, and atomic formulas `w(y) = 1` have the same truth
value in `H` and in `S`.

For the marked-group form: a basic clopen neighbourhood of a marked
`n`-generated group in the space of marked groups is given by finitely many
words required to be trivial and finitely many required to be non-trivial
(CGP, proof of Proposition `prop skeleton dense`, lines 794–797). If `H` is a
limit of marked finitely generated subgroups of members of `K`, one such
subgroup satisfies the relators `r_i` and keeps every `f_i` non-trivial, so
`Σ_H` holds in a member of `K` and `H` embeds there by (⇐). `∎`
