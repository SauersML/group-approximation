---
rg: 2
id: torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical
kind: claim
title: Some torsion-free LEF Kazhdan group has a finitely presented mapping torus whose MF radical is the whole kernel
distinct_from:
  mf-kazhdan-quotientless-mapping-torus-exact-radical: that is (XMF) for an arbitrary MF kernel, with no torsion-freeness, LEF or finite presentation; this is its torsion-free, LEF, finitely presented specialization, which alone is equivalent to the flagship witnesses lying in the permanence closure.
  exact-kazhdan-radical-kernel-cannot-be-lef: that states (EKL1); this asserts a torsion-free, finitely presented counterexample to it.
  lef-kazhdan-group-without-finite-quotients-exists: that group is LEF, Kazhdan and quotientless but torsion-generated; this needs a torsion-free kernel and an automorphism with exact radical.
  torsion-free-lef-kazhdan-non-rf-seed: that seed is torsion-free, LEF and Kazhdan but has finite quotients, so its mapping-torus radicals stay inside its centre.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that asks for a sofic kernel with an extrinsic compression defect; this asks for a LEF kernel and a bare radical equation, with soficity automatic.
artifacts:
  - research/quotient-permuting-and-ambient-inner-mapping-tori-are-lef.md
  - research/char-zero-subshift-elementary-group-is-lef-kazhdan-quotientless.md
  - research/kazhdan-gapped-mapping-torus-models-are-lef-quotients.md
  - research/kazhdan-multiplicity-rigidity-kills-exact-cover-models.md
---

**OPEN.** There exist a nontrivial finitely generated group `K` and `φ ∈ Aut(K)` such that

```text
(LK1)  K is torsion-free, LEF and has property (T);
(LK2)  G = K ⋊_φ Z is finitely presented;
(LK3)  Rad_MF(G) = K × {0}.
```

**Why it matters.** By `permanence-closure-radical-witnesses-have-lef-kernels`, this claim is
exactly the part of `torsion-free-sofic-exact-mf-radical-over-z` whose witnesses lie in the sofic
permanence closure. Here soficity comes for free, and the route
`torsion-free-sofic-exact-mf-radical-via-lef-kernel` closes the flagship from this claim alone. Every
other witness needs a non-LEF sofic Kazhdan kernel certified outside the permanence closure.

**Forced structure** (from the established claim). Any solution has these properties:
- `K` is MF with `Rad_MF(K) = 1`;
- `K` has no nontrivial finite quotient and is not finitely presented;
- `[φ]` has infinite order in `Out(K)`;
- `G` is sofic, non-MF, and not LEF.

**Prerequisites, each of which can fail on its own.**
- **(L1)** A torsion-free LEF Kazhdan group without nontrivial finite quotients exists. This is unknown.
  - `lef-kazhdan-group-without-finite-quotients-exists` fails torsion-freeness, and so does every
    elementary group `EL_n(R)` with `n ≥ 3`, by `steinberg-images-die-in-torsion-free-groups`.
  - `torsion-free-lef-kazhdan-non-rf-seed` fails quotientlessness.
  - The live programs are these:
    - the torsion-free alternating-mother limits of `torsion-free-kazhdan-alternating-mother-limit-gate`;
    - the relation-module covers of `kazhdan-rational-relation-cover-reduction`, provided the cover
      stays LEF.
- **(L2)** (EKL1) fails for that kernel. Any argument for (EKL1) would kill this claim outright. The
  periodization attempt of `mf-kazhdan-quotientless-mapping-torus-exact-radical` (Attempt 1) records why
  the obvious MF-construction for `G` dies at the wrap. So (L2) is not known to fail.
- **(L3)** A finite automorphic presentation of a kernel which is itself not finitely presented. See
  `fp-mapping-torus-iff-finite-automorphic-presentation`.

**Finite-model reading of (LK3).** `K` is a marked limit of finite groups `F_n`. These are uniformly
Kazhdan, since they eventually become quotients of one finitely presented Kazhdan cover. (LK3) says no
sequence of almost-representations of `G` in the norm corona can be faithful on `K`. A natural first test
case is (L1)-(L2) for a torsion-free alternating limit with `φ` induced by an automorphism of the mother
group that permutes the quotient sequence.

## Attempts

**Attempt 1 (swarm-0917 w12-titz-follow): the first test case and standard automorphisms. Dead for
these classes; the claim stays OPEN.**

- **The suggested test case is dead.** By (B) of `quotient-permuting-and-ambient-inner-mapping-tori-are-lef`,
  an automorphism of a finitely generated mother `M` that permutes a sequence of finite quotients has
  finite orbits. This is because `M` has only finitely many normal subgroups with a given finite
  quotient. Intersecting over the orbits gives an invariant finite quotient family converging to `K`,
  so `G` is a marked limit of finite groups `(M/L_i) ⋊ Z/c_i`. `G` is LEF, and (LK3) fails. The
  "shift" `N_(n+1) = α(N_n)` needed at the wrap cannot occur. So (L2) cannot be reached by choosing the
  mother automorphism, for any `K`, torsion-free or not.
- **Ambient virtual innerness is dead.** By (C), if a power of `φ` is inner in a LEF group containing
  `K`, then `G` is LEF. For elementary kernels `EL_n(R)` over rings with integral or finite-field
  periodic models, this kills:
  - conjugation by diagonal units;
  - `EL_n(σ)` for every ring automorphism `σ` with an inner power, including those induced by
    `ψ ∈ Aut(X,T)` with `ψ^r ∈ <T>`, and the finite-spatial-class automorphisms of
    `subshift-diagonal-automorphisms-need-infinite-spatial-class`.
- **Characteristic-zero base for (L1).** `char-zero-subshift-elementary-group-is-lef-kazhdan-quotientless`
  shows that `Q_0 = EL_3(LC(X,Z) ⋊ Z)` is LEF, Kazhdan and quotientless, with root elements of infinite
  order. It still has 2-torsion, so it does not give (L1). Relation covers over it evade (RE) at root
  elements. They still die at the permutation-module envelope, by
  `relation-cover-sofic-envelope-forces-trivial-kernel` item 2.
- **Tried and unresolved.** A characteristic-zero analogue of (RE) at the sign element, via the lift
  `W = e_12(j) e_21(-j) e_12(j)` with `j ∈ J` and `j + a = 1` for a congruence ideal `J`. Whether
  `W^4 ∈ R_sat` is open.
- **What is left for (L2).** An automorphism with no power inner in any LEF overgroup of `K`, and with
  no invariant approximating family in any mother presentation. For elementary kernels, this means a
  nonstandard automorphism, or `EL_n(σ)` with `σ` of infinite order modulo inner automorphisms, e.g.
  induced by `ψ ∈ Aut(X,T)` of infinite order modulo `<T>`.

**Attempt 2 (swarm-0917 w15-titz-break): the corner route to (LK3) over rank-function rings. Dead for
this class; the claim stays OPEN.**

- **The class.** The only established tool that proves `Rad_MF ⊇` a nontrivial subgroup by compression
  is `kazhdan-centralizer-commuting-conjugates-kill-derived-subgroup`. Its matrix form over a ring `R`
  inside `GL_n(R) ⋊_σ Z` places:
  - the Kazhdan block `L` on a corner `f`;
  - the lamp `C` on an orthogonal corner `e`;
  - a compressor `u = h_0 π t^m`.

  This is a corner certificate.
- **Where every member dies.** (KC0) read entrywise gives `τ(e) = τ(e)(f - τf)(1 + w)`. So
  `rk(e) ≤ rk(f) - rk(τ f)` for every `τ`-invariant Sylvester rank function. One `σ`-invariant rank
  function exists as soon as any rank function does (averaging), and it forces `e` into its proper null
  ideal. See `corner-kc-certificates-die-at-invariant-rank-functions`.
- **What this kills.**
  - Over `LC(X,F_q) ⋊ Z` and `LC(X,Z) ⋊ Z`, which are simple or residually simple with rank functions,
    there is no nontrivial corner certificate in any subgroup of `GL_n(R) ⋊_σ Z`, for any `σ`.
  - This includes the residual (L2) automorphisms induced by `ψ ∈ Aut(X,T)` of infinite order modulo
    `<T>`, and every torsion-free Kazhdan subgroup of these linear groups.
- **What survives.**
  - Compressors `u` that mix coordinates non-monomially.
  - Centralizers that do not come from orthogonal corners.
  - Coefficient rings in which the lamp corner is null for every invariant rank function, which is
    the Hilbert-hotel, rank-function-free side. There, soficity of the kernel is the open problem.
  - Proofs of (LK3) that do not go through compression certificates at all.

**Attempt 3 (swarm-0917 w17-titz-follow): gapped corona models of `G`, with an arbitrary wrap
unitary. Dead for this class. (LK3) splits into a gapped half and a non-gapped half; the claim stays
OPEN.**

- **The class.** Homomorphisms `π : G -> U(Q)` whose kernel part lifts to spectrally gapped
  representations `U_i` of the free group `F(S)`. Gapped means that `‖U_i(g) − 1‖ ≥ c` whenever
  `U_i(g) ≠ 1`. The unitary `π(t)` is arbitrary. The class contains:
  - permutation models, including `ℓ²(Π/Λ)` blocks and Gassmann pairs;
  - sums of regular representations of any LEF sequence of `K`;
  - rational-character and bounded-exponent models;
  - wraps that are neither permutations nor block-monomial.

  It contains the regular-block class of `kazhdan-regular-block-periodizations-of-mapping-tori-are-finite`,
  together with two of its three survivors.
- **Where every member dies.** The kill is `kazhdan-gapped-mapping-torus-models-are-lef-quotients`.
  - (SR1): any unitary `T` with `max_s ‖T U(s) T* − U(w_s)‖ < κ` gives `Supp U = Supp (U ∘ ŵ)`.
    Here `U` is any finite-dimensional representation of Shalom's finitely presented Kazhdan cover
    `K~`, and `κ` is its Kazhdan constant.
  - The proof: property (T) on `HS(H_σ, H)`, applied to the almost invariant vector `T J`.
  - Hence `ker U = ker (U ∘ ŵ)`, and `ŵ` induces an automorphism of the image `U(F)`.
  - With a gap, the relators of `K` become exact, and the images converge to a `φ`-invariant
    quotient `K/N` carrying stage lifts. By `lef-mapping-torus-iff-stage-liftable-automorphism`,
    `(K/N) ⋊ Z` is LEF, and `k ∉ N`.
- **What this kills.** For a witness, no gapped model of `K`, for instance the LEF embedding
  `[λ_(F_i)]`, is `φ`-covariant in `Q`, under any unitary. Exactly:

  ```text
  gapped MF residual of G on K  =  LEF residual  (SR3).
  ```

- **The new decomposition.** (LK3) is equivalent to (LK3-gap) together with (LK3-ng). Each can fail
  on its own.
  - **(LK3-gap)** is equivalent to (NSL+): for every `φ`-invariant `N ⊊ K`, `φ̄` is not stage-liftable
    on `K/N`. This is purely combinatorial. It is (NSL) strengthened to every invariant quotient.
  - **(LK3-ng)** says that no non-gapped homomorphism is nontrivial on `K`.
- **What survives.** Kernel models with no gapped lift, where the MF-ness must come from spectral
  clustering at `1`:
  - lifts in which the relators hold only approximately;
  - exact lifts with finite images of growing order and irrational characters;
  - exact lifts with infinite images.

  So (EKL1) needs either (NSL+) to fail, which is combinatorial, or a non-gapped covariant model.
  No argument confined to permutation, regular or rational models can prove (EKL1) otherwise.
**Attempt 3 (swarm-0917 w22-titz-last1, stability-approximation): multiplicity rigidity at the
wrap. The exact-cover class is dead. (LK3) is reformulated as relative liftability. The claim
stays OPEN.** See `kazhdan-multiplicity-rigidity-kills-exact-cover-models` (ESTABLISHED).

- **The class.** Operator-norm models of `G` whose `K`-part lifts to exact representations of the
  finite-radius cover `K~_1 = <S | R_0 ∪ ŵ(R_0)>`. Blocks, images and the wrap unitary `T` are
  arbitrary. For LEF `K`, this includes `[π_n ∘ ι_n]` for local embeddings `ι_n` into finite
  groups `Q_n` and any representations `π_n` of `Q_n`. That covers the very models of
  `lef-implies-operator-mf` which make `K` MF. By (GP), it also includes `R_0`-exact permutation
  blocks, Gassmann blocks among them, with any `T`. This removes the block-monomial and regularity
  hypotheses of `kazhdan-regular-block-periodizations-of-mapping-tori-are-finite`.
- **The invariant.** The multiplicities `m_σ` over irreducible `σ` of the Kazhdan cover. The
  operator-norm Kazhdan projection on `ρ ⊗ σ̄` moves by less than `1` under a perturbation of size
  `δ_0 = 1/⌈4q ln 4/κ²⌉`, in every dimension.
- **Where every member dies.** At the wrap. `T U T*` and `U ∘ ŵ` are exact representations of
  `K~`, so they are equivalent, and `T` can be replaced by an exact intertwiner. The pair then
  satisfies the finite presentation of `G`, so it factors through `K`. Malcev (or finiteness of
  the image) then kills a quotientless `K`.
- **What this gives for (LK3).** By (RL), with (LK1) and (LK2) given, (LK3) is equivalent to the
  following: every norm-corona model of `G` lifts, on `K`, exactly on the finite set `R_1`. So a
  refutation of (LK3) for a candidate needs a model whose `K`-part is norm-unstable for `K~_1`: an
  asymptotic representation not asymptotic to genuine ones. LEF-type exact local data never gives
  one.
- **What survives.** Genuinely non-exact almost-representations of `K~_1`. (MR) says nothing about
  them. The obstruction to (LK3) is therefore exactly norm instability of a finitely presented
  Kazhdan cover at points factoring through `K`.

**Attempt 4 (swarm-0917 w23-titz-follow, operator-algebras): audit of the survivors of Attempt 3.
No new class is killed. Two lifting reformulations coincide, and the lifting and winding shortcuts
are dead. The claim stays OPEN.**

- **(U) ucp form of (RL).** Let `K` be Kazhdan and quotientless, `φ` arbitrary (no finite
  presentation needed). Then `Rad_MF(G) ⊇ K` iff every norm-corona model `Θ` of `G` has
  `Θ|_(C*(K))` ucp-liftable to `∏ M_(k_n)`. Forward: a model trivial on `K` lifts by `x ↦ ε(x)·1`.
  Backward: a ucp lift of a *-homomorphism into `∏/⊕` is asymptotically multiplicative, so Remark W
  of `local-mf-stability-splits-into-rounding-gap-and-path-connection` gives `Θ(u_s) = 1`.
  Together with (RL), for one model: R_1-liftable on `K` ⟺ ucp-liftable on `C*(K)` ⟺ trivial on `K`.
  So the survivors of Attempt 3 are exactly the models that are not ucp-liftable on `C*(K)`. For
  LEF `K` such kernel models exist, by `quotientless-lef-kazhdan-corona-trace-has-no-ucp-lift`.
  What is open is whether one of them extends over `φ`.
- **Dead shortcut 1: the LLP.** If `C*(G)` or `C*(K)` had Kirchberg's LLP, every `Θ` would lift:
  local ucp lifts on finite-dimensional operator systems `E_j ↑`, extended to `C*(K)` by Arveson
  in each `M_(k_n)`, glue diagonally. By (U), `Rad_MF(G) ⊇ K` would then hold for every `φ`. But
  `C*(K)` is a conditionally expected subalgebra of `C*(G)`, so both cases give the LLP for `C*(K)`.
  `K` is Kazhdan and not residually finite, so `llp-non-rf-kazhdan-group-is-non-hyperlinear` makes
  it non-hyperlinear. That contradicts (LK1), since `K` is sofic. So every witness has
  `C*(G)` without the LLP, and (LK3) needs a lifting property of norm-corona models only. That
  property is not a C*-property of `C*(G)`.
- **Dead shortcut 2: windings.** A winding functional of a `G`-model is a homomorphism on
  `H_2(K; Z)` with `W ∘ φ_* = W`. So it factors through `H_2(G) ≅ H_2(K)_φ`, by the Wang sequence
  and `H_1(K) = 0`. `mf-radical-is-blind-to-degree-two-windings` makes every survivor
  winding-free after realification. So no winding certifies that a survivor is trivial, and none
  certifies that it is nontrivial.
- **Dead shortcut 3: torus-level (WK).** Take any central extension `1 -> Z -> G~ -> G -> 1`.
  `[K~, K~]` of the preimage `K~` of `K` is a nontrivial perfect central extension of `K`. It is
  quotientless: a finite quotient, modulo the image of the centre, is a finite quotient of `K`, so it
  is cyclic, and being perfect it is trivial. `G~` is finitely presented, so if it were LEF it would
  be residually finite, and so would its nontrivial quotientless subgroup `[K~, K~]`. That is
  impossible. So LEF central-extension refutations in the style of
  `mf-stable-kernels-lack-lef-nonsplit-central-extensions` never apply to the torus. They apply
  only to `K` itself, which is not finitely presented.
- **Next falsifiable step.** Every LEF-derived kernel model is R_1-liftable, so Attempt 3 already
  kills its wraps. This includes the non-ucp-liftable model of
  `quotientless-lef-kazhdan-corona-trace-has-no-ucp-lift`. A refutation of (LK3) therefore needs a
  kernel model `Θ_0` that is neither R_1-liftable nor ucp-liftable, together with a corona unitary
  `T` such that `T Θ_0(s) T* = Θ_0(w_s)`. The first test is a sharper question: is some
  asymptotic `K`-representation of a LEF candidate at positive distance from every exact
  representation of `K~_1`? If there is none, (LK3) holds for that candidate.
