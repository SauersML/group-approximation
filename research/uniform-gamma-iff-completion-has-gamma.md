---
rg: 2
id: uniform-gamma-iff-completion-has-gamma
kind: claim
title: A separable C*-algebra with compact trace space has uniform property Gamma iff its uniform tracial completion has property Gamma
distinct_from:
  bauer-uniform-gamma-iff-trivial-tracial-bundle: that identifies uniform Gamma with triviality of the R-fibre bundle for simple algebras with Bauer simplex; this transfers uniform Gamma to the tracially complete completion for any compact trace space.
---

Let `A` be a separable C*-algebra with `T(A)` compact. Then the following are equivalent:
- `A` has uniform property Γ in the sense of Castillejos–Evington–Tikuisis–White, Definition 2.1;
- its tracial completion `(M, X)` with respect to `T(A)` has property Γ in the sense of CCEGSTW
  Definition 5.19.

In CCEGSTW's definition, property Γ means: for every `‖·‖_{2,X}`-separable `S ⊆ M` and every `k`,
there are projections `p_1, …, p_k ∈ M^ω ∩ S'` summing to `1` with `τ(a p_i) = τ(a)/k` for all
`a ∈ S` and all `τ ∈ X^ω`. Here `X^ω` is the closed convex hull of the limit traces.

Import: route `uniform-gamma-iff-completion-has-gamma-citation`.
