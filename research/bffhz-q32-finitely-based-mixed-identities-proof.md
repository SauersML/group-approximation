---
rg: 2
id: bffhz-q32-finitely-based-mixed-identities-proof
kind: route
title: Read finitely many normal generators of the kernel as mixed identities, push the kernel into any overgroup satisfying them, and detect the rest of the identities with transvections
target: bffhz-q32-forces-finitely-based-mixed-identities
requires:
  - a2-kernel-removal-forces-recursive-kernel
---

Notation is as in the target. Automorphisms of `S * F_n` fixing `S` pointwise are
determined by the images of `x_1, ..., x_n`. For `M ⊇ S`, every map from
`{x_1, ..., x_n}` to `M` extends uniquely to an element of `X_M`, so `X_M ≅ M^n`.
`A` acts on `X_M` by precomposition, `φ -> φ ∘ α`.

## Part (A)

**Step 0 (normal generators).** `A` is finitely presented
(`a2-kernel-removal-forces-recursive-kernel` (c), from BFFHZ Proposition 1.1 for
the centerless group `S`). Only finite generation of `A` is used here.
- Write `A = F/R` with `F` free on a finite generating set of `A`, and
  `A/K = F/N` with `N ⊇ R`.
- Since `A/K` is finitely presented, finite presentability does not depend on
  the finite generating set (B. H. Neumann's lemma). So `N` is the normal closure
  in `F` of finitely many elements.
- Their images `k_1, ..., k_r` normally generate `K = N/R` in `A`.

**Step 1 (kernel criterion).** `φ ∘ α = φ` iff the two homomorphisms agree on the
generators. On `S` both are the inclusion, so this means
`φ(x_i^-1 α(x_i)) = 1` for every `i`. Hence

```text
α in K_M   iff   x_i^-1 α(x_i) in J_n(M; S)   for i = 1, ..., n .
```

**Step 2 (monotonicity).** Composing with the inclusion `S -> M` puts `X_S` inside
`X_M`. So `J_n(M; S) ⊆ J_n(S)` and `K_M ⊆ K`.

**Step 3 (the basis).** Put `W = { x_i^-1 k_j(x_i) : 1 <= i <= n, 1 <= j <= r }`.
- `W` is finite, and `W ⊆ J_n(S)` by Step 1 with `M = S`.
- If `M` satisfies `W`, then every `k_j` lies in `K_M` by Step 1.
- `K_M` is the kernel of an action, hence normal in `A`, so it contains the
  normal closure `K`.
- With Step 2, `K_M = K`. This is conclusion 1.

**Step 4 (transvections).** Let `k <= n - 1` and `u in J_k(S)`, a word in `S` and
`x_1, ..., x_k`.
- *The transvection.* Let `τ_u` fix `S` and `x_1, ..., x_(n-1)`, and send `x_n`
  to `x_n u`. Since `u` does not involve `x_n`, `x_n -> x_n u^-1` gives the
  inverse, so `τ_u in A`.
- *It lies in the kernel.* By Step 1, `τ_u in K`: the only nontrivial quotient
  `x_n^-1 τ_u(x_n)` is `u`, and `u` is trivial under every substitution from `S`.
- *Pushing into `M`.* If `M` satisfies `W`, Step 3 gives `τ_u in K_M`, so
  `u in J_n(M; S)`.
- *Back to `k` variables.* Every `S`-homomorphism `S * F_k -> M` extends to
  `X_M` by sending `x_(k+1), ..., x_n` to `1`, and `u` involves only
  `x_1, ..., x_k`. So `u in J_k(M; S)`.

So `J_k(S) ⊆ J_k(M; S)`, and Step 2 in `k` variables gives equality. This is
conclusion 2. `∎ (A)`

## Part (B)

Let `N_W ⊴ S * F_k` be the normal closure of the instances `w(p_1, ..., p_m)`.
Here `w(p_1, ..., p_m)` means `σ(w)` for the `S`-homomorphism
`σ : S * F_m -> S * F_k` with `x_i -> p_i`.

**Instances vanish wherever `W` holds.** Let `M ⊇ S` satisfy `W` and let
`φ : S * F_k -> M` be an `S`-homomorphism. Then `φ ∘ σ` is an `S`-homomorphism
`S * F_m -> M`, so `φ(σ(w)) = 1`. Hence `N_W ⊆ J_k(M; S)`. With `M = S` this gives
`N_W ⊆ J_k(S)`.

**(2) ⟹ (1).** If `J_k(S) = N_W`, then every `M` satisfying `W` has
`J_k(S) = N_W ⊆ J_k(M; S) ⊆ J_k(S)`.

**(1) ⟹ (2).** Put `M = (S * F_k)/N_W` with projection `π`.
- *`S` embeds.* `S ∩ N_W ⊆ S ∩ J_k(S) = 1`, since a constant trivial under all
  substitutions is trivial. So `π` embeds `S`, and we identify `S` with `π(S)`.
- *`M` satisfies `W`.* An `S`-homomorphism `ψ : S * F_m -> M` sends each `x_i`
  to some `π(p_i)`, so `ψ = π ∘ σ` for the corresponding `σ`. Then
  `ψ(w) = π(σ(w)) = 1`.
- *Conclusion.* By (1), `J_k(S) ⊆ J_k(M; S)`. Evaluating `u in J_k(S)` at the
  `S`-homomorphism `π` itself gives `π(u) = 1`, i.e. `u in N_W`.

So `J_k(S) = N_W`. `∎ (B)`

## Part (C)

Let `S = <Y | R>` be a finite presentation. Then `S * F_k = <Y, x_1, ..., x_k | R>`.
- *r.e.* By (B), a word lies in `J_k(S)` iff it equals in `S * F_k` a product of
  conjugates of instances `w(p_1, ..., p_m)^(±1)`. Enumerating instances,
  products of conjugates, and consequences of `R` makes this set r.e.
- *co-r.e.* A word `u` is not in `J_k(S)` iff some tuple in `S^k` gives
  `u(s_1, ..., s_k) != 1` in `S`. The word problem of `S` is solvable, so this is
  r.e.

So `J_k(S)` is recursive. `∎ (C)`

## Contrapositive

Suppose `J_1(S)` is not finitely based over overgroups. Were `A/K` finitely
presented for some `n >= 2`, (A) conclusion 2 with `k = 1` would give a basis. So
it is not. `∎`
