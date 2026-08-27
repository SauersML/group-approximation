---
rg: 2
id: finite-central-extension-rf-iff-virtually-splits-proof
kind: route
title: Separate the finite kernel to get a section, and take a normal core to go back
target: finite-central-extension-rf-iff-virtually-splits
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Write `p : E_α → H` for the projection.  Statements (2) and (3) are the
standard `H^2` classification of central extensions, so only (1) ⟺ (3) needs
an argument.

**(1) ⟹ (3).**  `A` is finite, so for each `1 ≠ a ∈ A` residual finiteness of
`E_α` gives a finite-index normal subgroup missing `a`; intersect the finitely
many of them to get

```text
L ⊴_f E_α,   L ∩ A = 1.
```

Then `p|_L` has kernel `L ∩ A = 1`, so it is an isomorphism onto
`H_0 = p(L)`, which has finite index in `H` because `L` has finite index in
`E_α`.  Its inverse `H_0 → L ≤ E_α` is a homomorphic section of the extension
restricted to `H_0`.

**(3) ⟹ (1).**  Let `s : H_0 → E_α` be a section over `H_0 ≤_f H` and put
`K = s(H_0)`.  Then `[E_α : K] = [H : H_0] · |A| < ∞` and `K ∩ A = 1`.  The
normal core `K' = ∩_(e ∈ E_α) e K e^(-1)` is normal of finite index, and still
meets `A` trivially — `A` is central, so `A ∩ eKe^(-1) = e(A ∩ K)e^(-1) = 1`.
Hence `A` injects into the finite group `E_α / K'`, which separates every
nontrivial element of `A` from `1`.  Any `e ∈ E_α ∖ A` has `p(e) ≠ 1` and is
separated by composing `p` with a finite quotient of `H`.  So every nontrivial
element of `E_α` survives some finite quotient.

**The profinite half.**  If `α = c^*(β)` for `β ∈ H^2_cont(H_hat; A)`, realize
`β` by a profinite central extension `1 → A → E_tilde → H_hat → 1` and pull
back along `H → H_hat`; the pullback is `{(x,h) ∈ E_tilde × H : q(x) = ι(h)}`,
a subgroup of the residually finite group `E_tilde × H`, and it represents
`α`.  Subgroups of residually finite groups are residually finite.
