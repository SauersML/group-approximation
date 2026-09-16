---
rg: 2
id: mif-free-product-ascending-hnn-pbh-proof
kind: route
title: Normalize the automorphism by Kurosh, embed the mapping torus in the BFFHZ actor extended by a hat automorphism, and realize that hat by a normalizing permutation
target: mif-free-product-automorphism-ascending-hnn-is-pbh
requires:
  - relative-automorphism-of-fp-simple-mif-group-has-type-a-action
  - stable-permutation-hnn-of-type-a-actor-is-type-a
  - type-a-action-gives-boone-higman-for-subgroups
---

Automorphisms compose right to left, and `c_g(q) = g q g^-1`. `B_A` is the class
of groups embedding in a group with an action of type (A). It is closed under
subgroups by definition.

Fix `M` finitely presented, simple and MIF, `m >= 0`, `Q = M * F_m`,
`β ∈ Aut(Q)`, and `J <= Q` with `β(J) ⊆ J`.

## Step 0. It suffices to take m >= 1

Let `m = 0`, so `β = α ∈ Aut(M)` and `J <= M`. Put `Q' = M * <z>` and let
`hat(α) ∈ Aut(Q')` be `α` on `M` and the identity on `z`. It is the free product
of two automorphisms, hence an automorphism. Then `J <= Q'`,
`hat(α)(J) = α(J) ⊆ J`, and `hat(α)` restricts to `α` on `J`. So `J *_α` is
literally the group `J *_(hat(α))` for the data `(M, 1, hat(α), J)`. From now on
`m >= 1`, with free basis `z_1, ..., z_m`.

## Step 1. β carries M to a conjugate of M

**M is freely indecomposable and not free.**
- **Not free.** `M` is simple, so `M != 1`. A nontrivial free group surjects
  onto `Z`. For simple `M` the kernel would be trivial and `M ≅ Z`, but `Z` is not
  simple. So `M` is not free.
- **Freely indecomposable.** Suppose `M = A * B` with `A, B != 1`. The natural
  map `A * B -> A × B` is onto, and it kills `[a, b] != 1` for `a ∈ A \ 1`,
  `b ∈ B \ 1`. Its kernel is a nontrivial normal subgroup, so it is all of `M`
  and `A × B = 1`, a contradiction.

**Kurosh.** By the Kurosh subgroup theorem, every subgroup `H` of `Q = M * F_m`
is a free product `F * (*_i (H ∩ g_i M g_i^-1))` with `F` free. For `H = β(M)`,
which is isomorphic to `M`, free indecomposability leaves one nontrivial factor,
and it is not `F` because `M` is not free. Hence

```text
β(M) <= g M g^-1   and, applying the same to β^-1,   β^-1(M) <= h M h^-1
```

for some `g, h ∈ Q`.

**Equality.** Apply `β` to the second inclusion and use the first:

```text
M = β(β^-1(M)) <= β(h) β(M) β(h)^-1 <= w M w^-1,   w = β(h) g.
```

A free factor of a free product is malnormal: if `w ∉ M` then
`w M w^-1 ∩ M = 1` (normal form theorem for free products). Here
`w M w^-1 ∩ M = M != 1`, so `w ∈ M` and `w M w^-1 = M`. So both inclusions in
the display are equalities, and `β(h) β(M) β(h)^-1 = β(h) g M g^-1 β(h)^-1`.
Cancelling `β(h)` gives `β(M) = g M g^-1`.

## Step 2. Inner correction

Put `β₀ = c_g^-1 ∘ β`, so `β₀(q) = g^-1 β(q) g`. Then `β₀ ∈ Aut(Q)` and
`β₀(M) = M`, so `α = β₀|_M ∈ Aut(M)`.

**Q ⋊_β Z ≅ Q ⋊_(β₀) Z.** Write `Q ⋊_β Z = < Q, t | t q t^-1 = β(q) >` and
`Q ⋊_(β₀) Z = < Q, s | s q s^-1 = β₀(q) >`.
- `q -> q`, `s -> g^-1 t` respects the relations:
  `g^-1 t q t^-1 g = g^-1 β(q) g = β₀(q)`.
- `q -> q`, `t -> g s` respects the relations:
  `g s q s^-1 g^-1 = g β₀(q) g^-1 = β(q)`.
- The composites fix `Q` and send `s -> g^-1 g s = s` and `t -> g g^-1 t = t`.

So the two maps are inverse isomorphisms.

**Splitting off the hat.** Let `hat_Q(α) ∈ Aut(Q)` be `α` on `M` and the
identity on `z_1, ..., z_m`. Put `θ = β₀ ∘ hat_Q(α)^-1`. For `y ∈ M`,
`hat_Q(α)^-1(y) = α^-1(y) ∈ M` and `β₀(α^-1(y)) = α(α^-1(y)) = y`. So `θ` fixes
`M` pointwise, `θ ∈ Aut_M(Q)`, and

```text
β₀ = θ ∘ hat_Q(α).                                                  (N)
```

## Step 3. Embedding in the extended actor

Put `P = Q * <x> = M * F(z_1, ..., z_m, x)`, a free product of `M` with a free
group of rank `n = m + 1 >= 2`, and `Ω = Aut_M(P)`.

**Right transvections.** For `q ∈ Q` let `ρ_q` be the endomorphism of `P` that
fixes `Q` pointwise and sends `x -> x q`.
- `ρ_q ρ_r (x) = ρ_q(x r) = x q r`, because `ρ_q` fixes `r ∈ Q`. With both
  sides fixing `Q`, `ρ_q ρ_r = ρ_(qr)`. Also `ρ_1 = id`, so `ρ_q ∈ Ω` with
  inverse `ρ_(q^-1)`.
- `ρ_q = id` forces `x q = x`, so `q = 1`. Hence `ρ : Q -> Ω` is an injective
  homomorphism.

**Extensions.** For `θ ∈ Aut_M(Q)` let `tilde(θ) ∈ Ω` be `θ` on `Q` and the
identity on `x`. For `α ∈ Aut(M)` let `hat(α) ∈ Aut(P)` be `α` on `M` and the
identity on `z_1, ..., z_m, x`. Both are free products of automorphisms, and
`hat(α)` restricts to `hat_Q(α)` on `Q`.

**Conjugation formulas.** For `q ∈ Q`:

```text
tilde(θ) ρ_q tilde(θ)^-1 = ρ_(θ(q)),        hat(α) ρ_q hat(α)^-1 = ρ_(hat_Q(α)(q)).   (C)
```

Check the first on generators. On `Q`, `tilde(θ)^-1` maps `Q` to `Q`, `ρ_q`
fixes `Q`, and `tilde(θ)` maps back, so the composite is the identity on `Q`, as
is `ρ_(θ(q))`. On `x`: `x -> x -> x q -> x θ(q)`. The second is identical, with
`hat(α)` preserving `Q` and fixing `x`.

**hat(α) normalizes Ω.** For `ω ∈ Ω` and `y ∈ M`,
`hat(α) ω hat(α)^-1 (y) = hat(α)(ω(α^-1(y))) = α(α^-1(y)) = y`. So
`hat(α) ω hat(α)^-1 ∈ Ω`.

**The extended actor.** Let `E = Ω ⋊ <τ>` with `τ ω τ^-1 = hat(α) ω hat(α)^-1`.

**The map.** Define `Ψ : Q ⋊_(β₀) Z -> E` by `q -> ρ_q` and `s -> tilde(θ) τ`.
By (C) and (N),

```text
Ψ(s) Ψ(q) Ψ(s)^-1 = tilde(θ) ρ_(hat_Q(α)(q)) tilde(θ)^-1 = ρ_(θ(hat_Q(α)(q))) = ρ_(β₀(q)) = Ψ(β₀(q)).
```

So `Ψ` respects the defining relations and is a homomorphism.

**Ψ is injective.** Every element of `Q ⋊_(β₀) Z` is `q s^k` with `q ∈ Q`,
`k ∈ Z`. Since `τ` normalizes `Ω`, `(tilde(θ) τ)^k = ω_k τ^k` for some
`ω_k ∈ Ω`. So `Ψ(q s^k) = ρ_q ω_k τ^k`, whose image under `E -> Z` is `k`. If
`Ψ(q s^k) = 1`, then `k = 0`, so `ω_0 = 1` and `ρ_q = 1`, and `q = 1`.

## Step 4. The extended actor lies in B_A

**The BFFHZ action.** Let `X = Hom_M(P, M)` be the set of homomorphisms
`P -> M` restricting to the identity on `M`. Since `n >= 2`,
`relative-automorphism-of-fp-simple-mif-group-has-type-a-action` (BFFHZ Theorem
E) says that `Ω` acts on `X` by precomposition with an action of type (A). Write
the action as a left action, `λ(ω)(f) = f ∘ ω^-1`. Orbits on points and on pairs,
stabilizers and faithfulness are the same for the right action `f -> f ∘ ω`, so
this is again of type (A).

**The permutation.** Define `π : X -> X` by `π(f) = α ∘ f ∘ hat(α)^-1`.
- **Well defined.** For `y ∈ M`, `hat(α)^-1(y) = α^-1(y) ∈ M` is fixed by `f`,
  and `α(α^-1(y)) = y`. So `π(f) ∈ X`.
- **Bijective.** `f -> α^-1 ∘ f ∘ hat(α)` is a two-sided inverse, by the same
  check.
- **Normalizes the action.** For `ω ∈ Ω` and `f ∈ X`,

  ```text
  π λ(ω) π^-1 (f) = α ∘ (α^-1 ∘ f ∘ hat(α)) ∘ ω^-1 ∘ hat(α)^-1
                  = f ∘ (hat(α) ω hat(α)^-1)^-1 = λ(hat(α) ω hat(α)^-1)(f).
  ```

So `π` normalizes `λ(Ω)`, and conjugation by `π`, transported through the
faithful `λ`, is the automorphism `ω -> hat(α) ω hat(α)^-1` of `Ω`. Hence `E` is
exactly the group `Gamma ⋊_phi Z` of part (c) of
`stable-permutation-hnn-of-type-a-actor-is-type-a`, with `Gamma = Ω`, the set `X`,
and `t -> π`.

**Applying (c).** `Ω` has an element of infinite order, for example `ρ_(z_1)`:
`ρ_(z_1)^k = ρ_(z_1^k) != id` for `k != 0` by Step 3. So both branches of (c)
apply.
- If no nonzero power of `π` lies in `λ(Ω)`, then `E` acting on `X` through
  `τ -> π` is of type (A).
- Otherwise `E` embeds in a group with a type (A) action.

Either way `E ∈ B_A`. By Steps 2 and 3, `Q ⋊_β Z ≅ Q ⋊_(β₀) Z <= E`, so
`Q ⋊_β Z ∈ B_A`.

## Step 5. The ascending HNN extension

Let `G = J *_β = < J, t | t j t^-1 = β(j) (j ∈ J) >`.

**Normal form.** Every element of `G` has the form `t^-p j t^q` with `p, q >= 0`
and `j ∈ J`.
- The set of such elements contains `J` and `t^±1`, and it is closed under
  inverses: `(t^-p j t^q)^-1 = t^-q j^-1 t^p`.
- It is closed under products. The relations give `t^r j' = β^r(j') t^r` and
  `j t^-r = t^-r β^r(j)` for `r >= 0`, with `β^r(j) ∈ J`. So for `q >= p'`,
  `t^-p j t^q · t^-p' j' t^q' = t^-p (j β^(q-p')(j')) t^(q-p'+q')`, and for
  `q < p'` it is `t^-(p+p'-q) (β^(p'-q)(j) j') t^q'`.

**The map.** `j -> j`, `t -> t` defines a homomorphism `ι : G -> Q ⋊_β Z`, since
the relations of `G` hold in `Q ⋊_β Z`.

**Injective.** `ι(t^-p j t^q)` has image `q - p` under `Q ⋊_β Z -> Z`. If it is
trivial then `q = p`, and `t^-p j t^p = β^-p(j)` in `Q ⋊_β Z`. That is trivial
only for `j = 1`, since `β` is an automorphism.

So `G <= Q ⋊_β Z ∈ B_A`, and `G ∈ B_A`. If `J` is finitely generated, then `G`
is finitely generated, has solvable word problem and embeds in a finitely
presented simple group, by `type-a-action-gives-boone-higman-for-subgroups`
(Zaremsky, Corollary B), applied to `G` as a subgroup of an actor. Cases 1 and 2
of the target are `J = M`, `m = 0` and `J = Q`. ∎

## What the proof does not use

- **No kernel computation.** Faithfulness of `E` on `X` is never needed. When
  some power of `π` lies in `λ(Ω)`, part (c) passes to a finite-index subgroup
  `Ω × Z` instead.
- **No word-map lemma.** The only facts about MIF are the ones inside BFFHZ
  Theorem E.
