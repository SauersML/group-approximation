---
rg: 2
id: rank-three-finite-twisted-kazhdan-cone-is-sofic
kind: claim
title: The rank-three finite twisted Kazhdan cone, twisted by evaluation at the origin, is sofic
distinct_from:
  finite-twisted-kazhdan-cone-is-sofic: that asks the question for every rank r ≥ 3 and is refuted for r ≥ 5 by block subpairs; this is the rank-three case, where no 3-element block has a disjoint centralising element.
  block-subpairs-make-twisted-kazhdan-cones-nonsofic: that proves nonsoficity whenever a block subpair has a trace with nontrivial centraliser; this is the case where every block trace is all of Gamma.
---

**OPEN.**  Let `R_+ = F_q[x_1..x_d]` and `R = F_q[x_1^(±1)..x_d^(±1)]` with `d ≥ 3`.  Let
`Gamma = EL_3(R_+) ≤ G = EL_3(R) x| SL_d(Z)` be the rank-three Kun-Thom Theorem E pair.  Let
`psi : Gamma -> F = PSL_3(F_q)` be evaluation at the origin followed by projection.  Is

```text
T_3 = (F x Gamma) *_(Gamma_psi) G
```

sofic, for some prime power `q` and some `d ≥ 3`?  The companion case `r = 4`, `q ∈ {2, 3, 5}` of
[[finite-twisted-kazhdan-cone-is-sofic]] is equally open and would serve the same purpose.

**Why it matters.**  By [[block-subpairs-make-twisted-kazhdan-cones-nonsofic]], every twisted-diagonal cone
over a Theorem E pair of rank `r ≥ 5` is nonsofic, for every twist.  The same holds in rank four for
`q ∉ {2, 3, 5}`.  So the twisted-cone route of [[kazhdan-double-cones-add-one-sigma1-bit]] to
[[sofic-recognition-finite-presentations-is-pi2-complete]] survives only through these low-rank pairs.  By
[[twisted-diagonal-cones-need-a-profinitely-invisible-core]] it survives only through a twist with a
centreless invisible core, and `T_3` is the basic example.

**What is known.**
- `T_3` is not residually finite.
- Every finite-index level `G_1` has `psi(Gamma ∩ G_1) = F`, by (V5) of the invisible-core node.
- The only block subpair is `(G, Gamma)` itself, and `F` is centreless.

**What would decide it.**
- *Nonsofic.*  Find a subgroup `B ≤ G` with `C_F(psi(B ∩ Gamma)) ≠ 1` and `B *_(B ∩ Gamma) B` nonsofic.  Such a
  `B` must have infinite index and must not be normal.  If `B ∩ Gamma` has finite index in `Gamma`, for instance
  `ker ev_0`, then `B` must avoid most of the nonnegative compressors in `SL_d(Z)`, because `ker ev_0` and
  `SL_d(Z)` together generate `G`.  Relative groups `EL_3(R, I) x| Stab(I)` over ideals `I` vanishing at the
  origin are the candidates named in [[finite-twisted-kazhdan-cone-is-sofic]].
- *Sofic.*  Build sofic approximations of `T_3`.  They cannot come from finite quotients of `T_3`.  This would be the first soficity theorem for an
  amalgam over a Kun-Thom subgroup that is not a free factor.

## Attempts

- **w8-111r, 2026-09-18: hypersurface-level subpairs (obstruction).**
  - *Result.*  By [[divisor-level-subpairs-cannot-certify-rank-three-twisted-cone]], graded diagonal twists
    `B = D (EL_3(F_q[L]) x| H) D^-1` satisfy the centraliser condition.  Their origin image lies in the torus, and
    `B` is Kazhdan with `B ∩ Gamma` infranormal and not normal in `B`.  But `B ∩ Gamma` maps onto an infinite
    Borel subgroup over `F_q[x_2..x_d]`, so it is not Kazhdan.  The relative groups `EL_3(R, I) x| Stab(I)` fail
    too, for every ideal `I`: either `psi(B ∩ Gamma) = F`, or `B ∩ Gamma` has an infinite abelian quotient.
  - *Why.*  Both families shrink `psi(B ∩ Gamma)` by a level along a hypersurface, and that level becomes an
    infinite amenable quotient of the edge.
  - *What is left.*  A Kazhdan edge with a level only at the origin, such as `ker ev_0` or `ev_0^-1(Borel)`,
    inside a subgroup `B` that avoids the nonnegative compressors.  Or build sofic approximations.
  - *Graph.*  This node now feeds the route [[sofic-fp-completeness-from-rank-three-twisted-kazhdan-cones]].
- **w9-111, 2026-09-18: origin-level monomial subpairs (obstruction).**
  - *Result.*  By [[monomial-origin-level-subpairs-cannot-certify-rank-three-cone]], take
    `B = < U_k, H >` with `U_k` the monomial elementary matrices of degree `≥ k` and `H ≤ SL_d(Z)`.  Then
    `B = Ũ x| H` and `psi(B ∩ Gamma)` is `1` or `F`: it is `F` exactly when `cone(H · R_+^d)` contains a line.
    For every `B ⊇ U_k`, a line in `cone(H_B · R_+^d)` already forces `psi(C) = F`.  In the salient case
    with `H` infinite and pointed closure, `B` maps onto `F_q wr_X H` with `X` infinite, so it is not Kazhdan.
    The symmetric-square PSD candidate `Sym^2 SL_3(Z)` falls here.  With `H` finite, `C` is profinitely
    closed in `B`, so it cannot be infranormal and non-normal.
  - *Why.*  The exponent semigroup `P` grades `B ∩ EL_3(R)`.  Pointedness makes the grading discrete, and then
    the irreducibles of `P` give an infinite permutation-module quotient, or, for finite `H`, a degree
    filtration by finite-index normal subgroups.
  - *What is left.*  An infinite Kazhdan `H` whose cone `cone(H · R_+^d)` is salient but has a closure with a
    nonzero lineality space.  A test case is `Sym^2 SL_3(Z[√2])` on `Z^12`.  Also left: subgroups `B ⊇ U_k`
    that are not generated by `U_k` and monomial elements.
- **w10-111, 2026-09-18: Galois-twisted PSD candidate and the compressor lemma (obstruction).**
  - *Result.*  By [[galois-psd-monomial-subpair-has-no-infranormal-trace]], `H = Sym^2 SL_3(Z[√2])` on `Z^12`
    does realise the residual geometry: `K0` is salient, `K = PSD × Sym^2 R^3`, and the lineality space is the
    irrational `V_-`.  But for every `B_(H,k)` with salient `K0`, `C` is infranormal in `B` exactly when the
    nonnegative matrices `H ∩ M_d(N)` generate `H`.  For this `H` they form a group of order 6, so `C` is not
    infranormal and Theorem A never applies.  Property (T) of `Ũ` and `C` does not need to be decided.
  - *Why.*  A compressor `u σ` conjugates `e_ij(x^m)` to an element whose `(i, j)` entry has leading monomial
    `x^(σm)`, because `0 ∉ P`.  So `σ` must map the orthant into itself.  The orthant of `Sym_3(Z[√2])` is
    `{ X_+ ± X_- diagonally dominant }`, and that forces the columns of `g` to be integral.
  - *What is left.*  A monomial certificate needs an infinite Kazhdan `H ≤ SL_d(Z)` generated by nonnegative
    matrices, with `cone(H · R_+^d)` salient and non-pointed closure.  Deciding whether such an `H` exists
    settles every origin-level monomial subpair.  The kill is basis-dependent: `Sym^2 SL_3(Z[√2])` in a
    different lattice basis, whose simplicial cone some generating set of a finite-index subgroup preserves,
    would survive.  Otherwise the nonsofic side needs `B ⊇ U_k` with
    `B ∩ EL_3(R)` larger than `Ũ`.
- **w11-111, 2026-09-18: atoms of the exponent monoid (obstruction).**
  - *Result.*  By [[atomic-exponent-monoids-kill-monomial-kazhdan-subpairs]], the wreath quotient of (M3)
    needs only an infinite atom set `X` of the exponent monoid `P`, not a pointed closure.  So `B_(H,k)` with
    `H` infinite is not Kazhdan whenever `P` is atomic, and in particular whenever the lineality space `L` of
    `K` is rational and misses the orthant.  The (M5) geometry does occur with (T) over `Z`: `SL_3(Z)` on
    `Z^3 ⊕ Sym^2 Z^3` has `K0` salient and `K = R^3 × PSD`.  But its `L` is rational, so it dies.
  - *Why.*  A rational `L` gives an integral functional that is positive on `P`, through the pointed quotient
    `K / L`.  Atomicity then makes `X` span, and an infinite `H` then gives infinitely many atoms.
  - *What is left.*  A monomial certificate needs an infinite Kazhdan `H ≤ SL_d(Z)` with three properties:
    it is generated by nonnegative matrices, `K0` is salient, and `P` is non-atomic with a finite atom set.
    The last property holds only if `L` is irrational or meets the orthant.  The sharp open question: does
    nonnegative generation of a Kazhdan `H` force `P` to be atomic?
