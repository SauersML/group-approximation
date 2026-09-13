---
rg: 2
id: non-removable-a2-kernel-from-nonrecursive-mixed-identities
kind: route
title: A non-recursive set of k-variable mixed identities reduces to the Theorem C kernel by one transvection, and a non-recursive kernel cannot be removed
target: a2-pair-with-non-removable-kernel-exists
requires:
  - fp-simple-group-with-nonrecursive-mixed-identities
  - a2-kernel-removal-forces-recursive-kernel
artifacts:
  - research/artifacts/solve-mixed-identity-undecidable-2026-09-13.md
---

Let `Γ` be infinite, finitely presented and simple, with `J_k(Γ)` not recursive.
Put `n = k + 1` and `A = Aut_Γ(Γ * F_n)`, acting on `X = Hom_Γ(Γ * F_n, Γ)` with
kernel `K`. By `a2-kernel-removal-forces-recursive-kernel` (c), this is a type
`[A_2]` action of the finitely presented group `A`.

**Step 1 (transvections).** For `w in Γ * F_k`, in the letters `x_1, ..., x_k`,
let `α_w` fix `Γ` and `x_2, ..., x_n` and send `x_1` to `x_1 w(x_2, ..., x_(k+1))`.
It is an automorphism with inverse `x_1 -> x_1 w(x_2, ..., x_(k+1))^-1`.

**Step 2 (reduction).** `α_w in K` iff `ρ(x_1) w(ρ(x_2), ..., ρ(x_(k+1))) = ρ(x_1)`
for every `ρ in X`. As `ρ` ranges over `X ≅ Γ^n`, the tuple
`(ρ(x_2), ..., ρ(x_(k+1)))` ranges over `Γ^k`. So `α_w in K` iff `w in J_k(Γ)`.

**Step 3 (computability).** For a letter `a` from a finite generating set of `Γ`,
or `a = x_j^(±1)` with `j <= k`, let `r_a in A` send `x_1` to `x_1 a'` and fix
`Γ` and `x_2, ..., x_n`. Here `a' = a` for letters of `Γ`, and `a' = x_(j+1)^(±1)`
otherwise. There are finitely many `r_a`. Fix words for them once in a finite
generating set of `A`. Since `a'` never involves `x_1`, the composite
`r_(a_1) ∘ ... ∘ r_(a_m)` sends `x_1` to `x_1 a'_1 ... a'_m`. So `w -> α_w` is a
computable map from words to words, and it many-one reduces `J_k(Γ)` to `K`.
Hence `K` is not recursive.

**Step 4 (non-removability).** By `a2-kernel-removal-forces-recursive-kernel` (b),
if `(A, K)` sharply embedded in a type `[A_2]` pair with finitely normally
generated kernel, then `K` would be recursive. It is not, so `(A, K)` witnesses
the target. `∎`

This extends the one-variable encoding of `a2-kernel-removal-recursive-kernel-proof`
to `k` variables, as Attempt 5 of `a2-pairs-embed-in-a2-pairs-with-fng-kernels`
remarks.
