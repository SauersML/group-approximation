---
rg: 2
id: cantor-integer-maps-central-direction-via-lifted-thompson-t
kind: route
title: "Relative (T) of the centre of T-bar pushes forward to relative (T) of Z·1_C in C(C,Z) ⋊ V"
target: cantor-integer-maps-central-direction-has-relative-t
requires:
  - lifted-thompson-t-center-has-relative-t
  - lifted-thompson-t-embeds-in-cantor-integer-maps-by-v
---

Let `G = C(C,Z) ⋊ V` and let `ψ` be a cnd function on `G`. Let
`Φ : T̄ → G` be the embedding of `lifted-thompson-t-embeds-in-cantor-integer-maps-by-v`, which
satisfies `Φ(z) = (1_C, id)`.

Then `ψ ∘ Φ` is a cnd function on `T̄`. By `lifted-thompson-t-center-has-relative-t`, it is
bounded on `⟨z⟩`. Since `Φ(z^M) = M·1_C`,

```text
sup_M ψ(M·1_C) = sup_M ψ∘Φ(z^M) < ∞.
```

This is the target statement. ∎

The converse fails formally: `T̄` is a proper subgroup of `G`. So the premise is strictly more
specific, and it can be attacked inside a group whose quotient by the centre is the Haagerup group
`T`.
