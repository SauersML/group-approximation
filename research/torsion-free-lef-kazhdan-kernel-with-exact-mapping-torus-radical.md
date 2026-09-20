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
