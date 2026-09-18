---
rg: 2
id: deligne-lattice-almost-v-germ-group-proof
kind: route
title: Normal subgroups of a torsion-free finite-index subgroup of the Deligne lattice are central or of finite index; kill the central kernel of the germ map with the central-V lemma
target: deligne-lattice-in-almost-v-sits-in-one-germ-group
requires:
  - kazhdan-subgroups-of-almost-v-have-no-central-v-elements
  - almost-v-fw-subgroups-act-through-finitely-many-germs
  - thompson-v-has-haagerup-property
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - bhm-singfix-condition-forces-fp-germ-groups
  - simple-kazhdan-germ-extension-germ-group-proof
---

Notation as in the claim. `Gamma~` has property (T), and so does every finite-index
subgroup.

**Item 1.** `Z` is central in `Gamma~` and torsion-free. Apply
`kazhdan-subgroups-of-almost-v-have-no-central-v-elements`, item 2, to `Λ = Gamma~ <= H`.

**Normal subgroup dichotomy.** Let `Γ(3) <= Sp_2n(Z)` be the principal congruence subgroup
of level 3. It is torsion-free (Minkowski; textbook) and of finite index. Let
`Gamma_1 <= p^-1(Γ(3))` have finite index in `Gamma~`, and put `Z_1 = Z ∩ Gamma_1`, infinite
cyclic and central. **Every normal subgroup `N` of `Gamma_1` has finite index or lies in
`Z_1`.** Indeed, `p(N)` is normal in the lattice `p(Gamma_1)` of `Sp_2n(R)`, which has real
rank `n >= 2`. By Margulis's normal subgroup theorem (textbook, not re-read), `p(N)` is
finite or of finite index.
- If `p(N)` is finite, it is trivial because `Γ(3)` is torsion-free. So `N <= ker p`, and
  `N <= Z_1`.
- If `p(N)` has finite index, then `Gamma_1/N` is an extension of the finite group
  `p(Gamma_1)/p(N)` by the cyclic group `Z_1 N/N`. So it is virtually cyclic. It has (T),
  so it is finite, and `N` has finite index.

**Item 2.**
1. By `almost-v-fw-subgroups-act-through-finitely-many-germs`, item 1, there are a
   finite-index `Gamma'_0 <= Gamma~`, a finite set `F` fixed pointwise by it, and `h in H`
   with germ map `φ : Gamma'_0 -> ∏_{y in F} (Gamma'_0)_y` and `ker φ <= hVh^-1`. Put
   `Gamma_0 = Gamma'_0 ∩ p^-1(Γ(3))`, of finite index, and restrict `φ` to it. Then `F` is
   still fixed pointwise, the kernel is still in `hVh^-1`, and the dichotomy applies to
   `Gamma_0`. Put `Z_0 = Z ∩ Gamma_0`.
2. **`φ` is injective.** `ker φ` is normal. If it had finite index, `h^-1 (ker φ) h` would
   be an infinite Kazhdan subgroup of `V`, which contradicts
   `thompson-v-has-haagerup-property`. So `ker φ <= Z_0`. Its elements are central in
   `Gamma_0` and lie in `hVh^-1`. Apply the central-V lemma, item 2, to `Λ = Gamma_0`: they
   have finite order. `Z_0` is torsion-free, so `ker φ = 1`. In particular `F ≠ ∅`.
3. **One coordinate is injective.** Put `K_y = ker(φ_y)`. These are normal subgroups of
   `Gamma_0` whose intersection over `F` is `ker φ = 1`. Suppose no `K_y` is trivial. Each
   `K_y` of finite index contains a finite-index subgroup of `Z_0`. Each `K_y <= Z_0` is a
   nontrivial subgroup of the infinite cyclic `Z_0`, hence of finite index in it. The
   intersection of finitely many finite-index subgroups of `Z_0` is nontrivial, which is a
   contradiction. So some `φ_y` is injective on `Gamma_0`, and in particular on `Z_0`,
   whose nontrivial elements therefore have germs of infinite order at `y`.
4. **`y` is singular.** At a point outside `sing(E)`, the isotropy germ group of `E` is
   trivial or infinite cyclic (`simple-kazhdan-germ-extension-germ-group-proof`, step 4).
   `Gamma_0` is not abelian, since `p(Gamma_0)` has finite index in `Sp_2n(Z)`. So
   `y in sing(E)`.

**Item 3.** Theorem 2.1 at `n = 2` makes `SingFix_E({y},{y})` finitely presented, and
`bhm-singfix-condition-forces-fp-germ-groups`, item 3, passes this to `(E)_y`. `∎`
