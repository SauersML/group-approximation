---
rg: 2
id: torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel
kind: claim
title: Some finitely generated torsion-free sofic Kazhdan group without finite quotients is locally MF-stable in operator norm and has an automorphism with a finite two-sided automorphic presentation
distinct_from:
  automorphic-sofic-kazhdan-kernel-with-full-mf-radical: that asks for Rad_MF(K) = K; this asks only for no finite quotient plus operator-norm stability relative to finitely presented covers, which Rad_MF(K) = K implies. The kernel may be MF here, and is then LEF.
  torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical: that asks for a LEF kernel together with the exact torus radical as a separate condition; here the exact radical is a consequence of local MF-stability for every automorphism at once, and the kernel need not be MF.
  torsion-free-sofic-quotientless-kazhdan-group-exists: that is the gate (SQK) without stability or automorphism; this adds (LS) and (P2).
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that rules out local stability in the normalized Hilbert--Schmidt metric for every infinite hyperlinear Kazhdan group, so the HS analogue of (LS) fails for every candidate here; (LS) is in operator norm, where Rad_MF(K) = K already gives it.
artifacts:
  - research/locally-mf-stable-kazhdan-kernels-collapse-torus-radicals.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
  - research/mapping-torus-mf-radical-lies-in-finite-residual.md
  - research/local-mf-stability-splits-into-rounding-gap-and-path-connection.md
---

**OPEN.** There exist a finitely generated group `K`, with finite generating set `S`, and
`φ ∈ Aut(K)` such that:

```text
(P1') K is nontrivial, torsion-free, sofic and Kazhdan;
(Q)   K has no nontrivial finite quotient;
(LS)  K is locally MF-stable: for every finite set R of relators of K and every sequence
      b_i ∈ U(n_i)^S with ‖r(b_i) − 1‖ -> 0 for every relator r of K, some c_i ∈ U(n_i)^S
      with r(c_i) = 1 for all r ∈ R has max_s ‖b_i(s) − c_i(s)‖ -> 0;
(P2)  K has a finite two-sided automorphic presentation (FAP1) for φ.
```

The route `exact-mf-radical-over-z-via-locally-mf-stable-kernel` turns any such pair into a witness of
`torsion-free-sofic-exact-mf-radical-over-z`, through Corollary D3 of
`locally-mf-stable-kazhdan-kernels-collapse-torus-radicals`.

**The conditions fail separately.**
- (Q) is forced: every witness kernel has it, by `mapping-torus-mf-radical-lies-in-finite-residual`.
- (LS) is not forced. It holds for finite groups, which fail (Q). It holds whenever
  `Rad_MF(K) = K`, where the trivial representation rounds every sequence.
- (P1') and (Q) together are the gate `torsion-free-sofic-quotientless-kazhdan-group-exists`.
- (P2) is exactly finite presentation of the torus, by
  `fp-mapping-torus-iff-finite-automorphic-presentation`.

**Two regimes.**
- **Full radical.** If `Rad_MF(K) = K`, this is `automorphic-sofic-kazhdan-kernel-with-full-mf-radical`.
- **MF kernel.** If `K` is MF, then `K` is LEF by Corollary D2. A solution would then also refute
  (EKL1) of `exact-kazhdan-radical-kernel-cannot-be-lef`, because its torus radical is exact and its
  kernel is LEF.

Intermediate kernels, with `1 ≠ Rad_MF(K) ≠ K`, are also allowed.

**What (LS) costs for an MF kernel.**
- Every operator-norm MF model of `K` must round to exact representations `c_i` of every finitely
  presented cover `<S | R>`.
- Each `c_i` has a residually finite linear image. It sees the relators of `K` outside `R` only
  approximately, so it need not give a finite quotient of `K`. This is why (Q) and (LS) are compatible
  on paper.
- By Theorem D, no automorphism can wrap such a `c_i`, with defect below `κ` and `R` G-complete, into a
  torus model that sees `K`.
- It is not known whether a Kazhdan group with (Q) that is MF can satisfy (LS). This is the MF half of
  this hole.

## Attempts

- **2026-09-20, LS splits into gap and paths (stability-approximation, swarm-0917-w21-w21-titz-follow).**
  Node: `local-mf-stability-splits-into-rounding-gap-and-path-connection` (ESTABLISHED). The hole stays OPEN.
  - *Decomposition.* `(LS_R) ⟺ (Gap_R,θ) ∧ (Conn_R)` (Theorem S, no (T) needed). (Gap) is local: a
    sequence that stays within `θ` of `Hom(P_R)` must converge to it. (Conn) is global: every asymptotic
    K-representation is joined to `Hom(P_R)` by a uniform path.
  - *Consequences for a Kazhdan kernel with (Q).* Nearby exact representations of `P_R`, `R ⊇ R_0`, have
    the same constituents (Lemma R). Under (Gap) the constituents are therefore a homotopy invariant
    (Theorem H). Every finite approximation is eventually `D`-quasirandom and perfect (Corollary E1). Under
    (LS) the constituents of any rounding escape every finite set (Corollary E2).
  - *Tried: (T) + (Q) + (LS) ⇒ `Rad_MF(K) = K`, i.e. refute the MF half.* It dies at (Gap). Rounding is
    two-sided, `X ↦ b(g) X c(g)*`. The only available Kazhdan argument for it runs in Hilbert--Schmidt
    norm and loses `sqrt(dim σ)` per constituent. By E2 those dimensions go to infinity. Lemma R controls
    supports, not multiplicities.
  - *Neither known Kazhdan instability mechanism applies.* FFGS dimension deletion costs `O(1)` in
    operator norm. The Ozawa--Thom weak-QD argument needs an asymptotically multiplicative ucp lift on
    `C*(K)`, and Remark W shows that no nontrivial model has one. (LS) gives lifts only on `C*(P_R)`.
  - *Next falsifiable step.* For `EL_3(LC(X,F_q) ⋊ Z)`, build a uniform K-path family between two
    LEF-derived exact representations of some `P_R` with different supports. By Test (T-Gap) that kills
    (LS) for this kernel. Alternatively, prove (Gap) for it.
