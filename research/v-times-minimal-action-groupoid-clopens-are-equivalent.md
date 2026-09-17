---
rg: 2
id: v-times-minimal-action-groupoid-clopens-are-equivalent
kind: claim
title: Any two nonempty clopen sets of C times X are joined by a compact open bisection of G_V times a minimal transformation groupoid
distinct_from:
  halvable-groupoid-alternating-full-groups-are-perfect: that assumes every clopen set splits into two equivalent halves and concludes perfection of the alternating full group; this proves that all nonempty clopen sets form a single equivalence class for G_V times a minimal action groupoid, and concludes nothing about commutators.
  v-times-ample-full-groups-are-generated-by-transpositions: that proves F = S = A for G_V times any ample groupoid, with no minimality; this is a transitivity statement on clopen sets which fails without minimality of the second factor.
  fp-full-binary-cantor-groups-have-type-a-actions: that assumes a full group containing the standard binary V on C; this supplies the clopen transitivity that replaces the standard-V hypothesis on the unit space C times X.
---

**ESTABLISHED** by `v-times-minimal-action-groupoid-clopen-equivalence-proof`.
Not independently reviewed.

## Statement

Let `C = {0,1}^N` and let `G_V` be the groupoid of germs of Thompson's group `V`
on `C`. Let `Λ` be a group acting by homeomorphisms on a nonempty compact
metrizable totally disconnected space `X`, minimally (every orbit dense). Put
`H = Λ ⋉ X`, with arrows `(λ, x)` from `x` to `λx`, and `T = G_V × H` on the
unit space `Y = C × X`.

For any two nonempty clopen sets `U, U' ⊆ Y` there is a compact open bisection
`B` of `T` with `s(B) = U` and `r(B) = U'`.

No freeness, finite type, or finite generation is assumed.

## Use

`fp-v-times-minimal-action-full-groups-have-type-a-actions` combines this with
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`. The case consumed
by `boone-higman-via-v-times-aperiodic-sft-full-groups` is `Λ` finitely
presented and `X` a minimal free subshift of finite type.

## Where minimality enters

Without minimality the statement is false: if `Z ⊆ X` is a proper nonempty
clopen invariant set then `C × Z` and `C × X` are not equivalent, because every
arrow of `T` preserves `C × Z`.
