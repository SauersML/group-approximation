---
rg: 2
id: finite-outer-order-radical-witnesses-cross-alekseev-thom
kind: claim
title: An exact-radical-over-Z witness whose automorphism has finite outer order is virtually a direct-product witness with a finitely presented full-radical kernel, so it answers Alekseev--Thom Open Problem 6.1
distinct_from:
  fp-kernel-crosses-alekseev-thom-open-problem: that assumes the kernel is finitely presented; this derives finite presentation of the kernel from finite outer order of the automorphism alone, and shows the same witness can then be replaced by a direct product.
  finite-outer-order-mapping-torus-is-virtually-product: that finds the finite-index subgroup K x Z and concludes only MF-transfer; this adds finite presentation of K, the radical identity Rad_MF(K) = K, and the converse, so it characterizes the whole finite-outer-order region of the goal.
  torsion-free-sofic-exact-mf-radical-over-z: that is the open existence goal; this splits its witnesses by the outer order of the automorphism and places every finite-order witness inside Alekseev--Thom Open Problem 6.1.
artifacts:
  - research/finite-outer-order-radical-witnesses-cross-alekseev-thom-proof.md
  - research/corona-finite-index-radical-heredity.md
  - research/finite-outer-order-mapping-torus-is-virtually-product-proof.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
---

**ESTABLISHED** through `finite-outer-order-radical-witnesses-cross-alekseev-thom-proof`.

Call a pair `(G, K)` a **witness** if it satisfies `(TFZ1)` of
`torsion-free-sofic-exact-mf-radical-over-z`:
- `G` is finitely presented, torsion-free and sofic;
- `K` is nontrivial, normal in `G` and Kazhdan;
- `Rad_MF(G) = K` and `G/K ~= Z`.

Every witness is a mapping torus `G = K x|_phi Z`, where `phi` is conjugation by a lift `t` of `1`.
The class `[phi]` in `Out(K)` does not depend on the lift.

**Theorem (FO-AT).**

1. **(Descent to a product.)** Suppose `[phi]` has finite order `r` in `Out(K)`. Then `G` has a
   subgroup `H` of index `r` with `H ~= K x Z`. Moreover `(H, K)` is again a witness, with the same
   kernel.
2. **(Product witnesses.)** `(K x Z, K)` is a witness exactly when `K` is a nontrivial, finitely
   presented, torsion-free, sofic Kazhdan group with `Rad_MF(K) = K`, that is, with no nontrivial
   homomorphism to any MF group.
3. **(Alekseev--Thom.)** Such a `K` is finitely presented, sofic and Kazhdan, and it has no
   nontrivial finite quotient; in particular it is not residually finite. So it answers Open
   Problem 6.1 of Alekseev--Thom (`fp-sofic-kazhdan-group-not-residually-finite`) positively.
4. **(Dichotomy.)** Every witness satisfies at least one of the following:
   - (AT) `K` is finitely presented, and then `K` answers Alekseev--Thom 6.1;
   - (IO) `K` is **not** finitely presented, no nonzero power of `phi` is inner, and `K` has a
     finite two-sided automorphic presentation `(FAP1)` for `phi`.

   The case `[phi]` of finite order always falls under (AT), by parts 1 to 3.

For every `n != 0`, `(K x|_(phi^n) Z, K)` is again a witness, because that subgroup has index `|n|`
and part 1's radical argument applies to it. So case (IO) is stable under passing to powers.

## Consequences for the goal cone

- **Two of the three graph routes are pure Alekseev--Thom instances.** The defect-core route takes
  `phi = id`, and the Titz--Witzel route takes `phi = id` on a finitely presented kernel. Both land
  in case (AT). This was known for those two routes separately. Part 2 says more: after passing to
  a finite-index subgroup, **every** finite-outer-order witness is a product witness of this kind.
  So no choice of automorphism of finite outer order can escape Alekseev--Thom 6.1. That includes
  every kernel with finite `Out(K)`.
- **The only region free of Alekseev--Thom 6.1 is (IO).** There the kernel is finitely generated
  but infinitely presented. Its automorphism has infinite outer order and carries a finite
  two-sided automorphic presentation. Combined with the descent theorem
  `mapping-torus-mf-radical-descends-through-kernel-radical`, (IO) splits once more:
  - **(IO-int)** `Rad_MF(K) = K`. The radical comes from `K` itself. A route to it is
    `exact-mf-radical-over-z-via-automorphic-full-radical-kernel`. Before this node, that branch
    had no route: the extrinsic route asks for a compression defect filling `K`, and the
    defect-core route asks for a finitely presented `K`.
  - **(IO-ext)** `K / Rad_MF(K)` is a nontrivial MF quotientless Kazhdan group whose induced
    automorphism has infinite outer order. This is
    `mf-kazhdan-quotientless-mapping-torus-exact-radical`, reached through the extrinsic-kernel
    route.
- **Calibration.** No route can be completed by an argument that stays inside the
  finite-outer-order region unless that argument also solves Alekseev--Thom 6.1. So every
  prerequisite confined to that region is at least as hard as 6.1.

## What is not claimed

- No witness is constructed, and the goal stays OPEN.
- Nothing is claimed about whether region (IO) is nonempty. In particular, the graph records no
  finitely generated sofic Kazhdan group with full MF radical. That existence is the first
  falsifiable step of (IO-int).
