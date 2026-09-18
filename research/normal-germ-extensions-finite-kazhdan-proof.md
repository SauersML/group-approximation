---
rg: 2
id: normal-germ-extensions-finite-kazhdan-proof
kind: route
title: Kazhdan subgroups of the germ groups are finite in both alternatives, so the FW germ map has finite image, and its kernel is a Kazhdan subgroup of a conjugate of V
target: normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups
requires:
  - almost-v-fw-subgroups-act-through-finitely-many-germs
  - normal-germ-extensions-of-thompson-v-contain-no-sl3z-proof
  - thompson-v-has-haagerup-property
---

Notation as in the claim. Standard facts about property (T): it passes to quotients and
to finite-index subgroups, and an abelian group with (T) is finite.

**Step 1. Kazhdan subgroups of germ groups are finite.** Let `p in C` and let
`K <= (G)_p` have property (T).
- *`p ∉ sing(G)`.* Every element of `G` fixing `p` agrees near `p` with an element of `V`,
  so `(G)_p = (V)_p`. By Lemma 2 of `normal-germ-extensions-of-thompson-v-contain-no-sl3z-proof`,
  `(V)_p` is trivial or infinite cyclic. So `K` is abelian, hence finite.
- *(a).* `(G)_p` is virtually `(V)_p`, hence virtually cyclic, and `K` is a virtually
  abelian group with (T). Its abelian finite-index subgroup is finite, so `K` is finite.
- *(b).* Lemma 4 of the same proof gives a homomorphism `ψ_p : (G)_p -> V(D) <= V` whose
  kernel `A_p` is abelian (it embeds in `C(D,Z)`). `ψ_p(K)` is a Kazhdan subgroup of `V`,
  hence finite by `thompson-v-has-haagerup-property`. So `K ∩ A_p` has finite index in
  `K`, has (T), and is abelian. It is finite, and so is `K`.

**Step 2. The theorem.** Let `Λ <= G` have property (T). `G <= H`, so by
`almost-v-fw-subgroups-act-through-finitely-many-germs`, item 1, there are a finite-index
`Λ_0 <= Λ`, a finite set `F` fixed pointwise by `Λ_0`, and `h in H` such that the germ map
`φ : Λ_0 -> ∏_{y in F} (G)_y` has `ker φ <= hVh^-1`. Each coordinate image `φ_y(Λ_0)` is a
Kazhdan subgroup of `(G)_y`, hence finite by Step 1. So `φ(Λ_0)` is finite, and `ker φ`
has finite index in `Λ_0`. Then `ker φ` has (T), and `h^-1 (ker φ) h` is a Kazhdan
subgroup of `V`, hence finite. So `Λ_0` is finite, and so is `Λ`. `∎`
