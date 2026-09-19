---
rg: 2
id: finite-outer-order-radical-witnesses-cross-alekseev-thom-proof
kind: route
title: Correct a power of the stable letter, restrict the radical to the product subgroup, and kill the central letter
target: finite-outer-order-radical-witnesses-cross-alekseev-thom
requires:
  - corona-finite-index-radical-heredity
  - mf-positive-controls
  - sofic-kernel-amenable-quotient-permanence
  - fp-kernel-crosses-alekseev-thom-open-problem
  - fp-mapping-torus-iff-finite-automorphic-presentation
---

Two standard facts of combinatorial group theory are used without further comment:
- (RS) a finite-index subgroup of a finitely presented group is finitely presented
  (Reidemeister--Schreier);
- (Q) if `P = <X | R>` is finitely presented and `w_1, ..., w_m in P`, then
  `P / <<w_1, ..., w_m>> = <X | R, w_1, ..., w_m>` is finitely presented.

Soficity passes to subgroups by restricting a sofic approximation. `Rad_MF` is the intersection
of the kernels of all homomorphisms to MF groups.

## Step 0: every witness is a mapping torus

`G/K ~= Z` is free, so a lift `t` of a generator splits the extension:
`G = K x|_phi Z` with `phi(k) = t k t^-1`. Another lift is `t' = a t` with `a in K`, and it changes
`phi` by the inner automorphism `Inn(a)`. So `[phi] in Out(K)` is well defined. Property (T) makes
`K` finitely generated.

## Step 1: part 1 (descent to a product)

Let `[phi]` have order `r >= 1` in `Out(K)`, so that `phi^r = Inn(a)` for some `a in K`. As in
`finite-outer-order-mapping-torus-is-virtually-product-proof`, put `s = a^-1 t^r`. For `k in K`,

```text
s k s^-1 = a^-1 phi^r(k) a = a^-1 (a k a^-1) a = k,
```

so `s` centralizes `K`. The exponent map `G -> Z` sends `s` to `r != 0`. So `<s>` is infinite
cyclic and meets `K` trivially, and `H = <K, s> = K <s>` is an internal direct product
`K x <s> ~= K x Z`. `H` is the full preimage of `rZ`, so `[G : H] = r`.

Now check that `(H, K)` is a witness:
- `H` is finitely presented by (RS);
- `H` is torsion-free and sofic, being a subgroup of `G`;
- `K` is unchanged, so it is nontrivial, normal in `H` and Kazhdan;
- `corona-finite-index-radical-heredity` gives
  `Rad_MF(H) = H ∩ Rad_MF(G) = H ∩ K = K`;
- `H / K ~= <s> ~= Z`.

The same computation, with `H_n = <K, t^n>` of index `|n|`, gives the closing remark that
`(K x|_(phi^n) Z, K)` is a witness for every `n != 0`. It does not use finite outer order.

## Step 2: part 2 (product witnesses)

Write `P = K x Z` with projections `p_K` and `p_Z`.

*Witness implies the listed properties of `K`.* Suppose `(P, K x {0})` is a witness.
- `P` is finitely presented, and `K ~= P / <<(e, 1)>>`, where `e` is the identity of `K` and `1` generates `Z`. So `K` is finitely presented by (Q).
- `K` is torsion-free and sofic, being a subgroup of `P`. It is nontrivial and Kazhdan by
  hypothesis.
- Let `f : K -> M` be any homomorphism to an MF group. Then `f ∘ p_K : P -> M` kills
  `Rad_MF(P) = K x {0}`. On `K x {0}` the map `f ∘ p_K` is `f`, so `f` is trivial. Hence
  `Rad_MF(K) = K`.

*The listed properties imply a witness.* Suppose `K` is nontrivial, finitely presented,
torsion-free, sofic and Kazhdan, with `Rad_MF(K) = K`.
- `P` is finitely presented: take the union of the two presentations and add the commutators of
  the generators of `K` with the generator of `Z`.
- `P` is torsion-free, since both factors are.
- `P` is sofic by `sofic-kernel-amenable-quotient-permanence`, with sofic kernel `K x {0}` and
  quotient `Z`.
- **Upper bound.** `Z` is residually finite, hence MF by `mf-positive-controls`. So
  `Rad_MF(P) <= ker p_Z = K x {0}`.
- **Lower bound.** For any `F : P -> M` with `M` MF, the restriction `F|_(K x {0})` is a
  homomorphism from a copy of `K` to `M`. It is trivial because `Rad_MF(K) = K`. So
  `K x {0} <= Rad_MF(P)`.
- `P / (K x {0}) ~= Z`.

## Step 3: part 3 (Alekseev--Thom)

Let `K` be as in part 2.
- Every finite group is residually finite, hence MF by `mf-positive-controls`. So every
  homomorphism from `K` to a finite group is trivial, and `K` has no nontrivial finite quotient.
- `K` is nontrivial, so it is not residually finite.
- `K` is finitely presented, sofic and Kazhdan.

This is a positive answer to Alekseev--Thom Open Problem 6.1. It is also the conclusion
`(ATK1)` of `fp-kernel-crosses-alekseev-thom-open-problem`, applied to the witness `(K x Z, K)`.

## Step 4: part 4 (dichotomy)

Let `(G, K)` be any witness.
- If `K` is finitely presented, `fp-kernel-crosses-alekseev-thom-open-problem` gives case (AT).
- Otherwise `[phi]` has infinite order in `Out(K)`: if its order were finite, Steps 1 and 2 would
  make `K` finitely presented. So no nonzero power of `phi` is inner.
- `G` is finitely presented and `K` is finitely generated. So
  `fp-mapping-torus-iff-finite-automorphic-presentation` gives `K` a finite two-sided automorphic
  presentation `(FAP1)` for `phi`. That is case (IO).

Finally, a finite-order `[phi]` falls under (AT) by Steps 1 to 3. `∎`
