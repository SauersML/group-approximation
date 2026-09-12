---
rg: 2
id: hs-block-gap-iff-liftable-masa-of-actor-commutant
kind: claim
title: A partition carries the consumed block gap of a Kazhdan actor exactly when it lifts a masa of the actor's relative commutant
distinct_from:
  hs-one-level-expander-block-decomposition: that asks for a one-level partition with vanishing boundary and a uniform scalar gap, and derives the consumed form (F2) under exact-centralizer capture; this proves that (F2) plus vanishing boundary is equivalent to the partition algebra being a maximal abelian subalgebra of the ultraproduct relative commutant, with the Kazhdan constant as gap constant and no capture hypothesis.
  centralizer-capture-controls-nonspiky-gap-failures: that eliminates bounded bad blocks under capture by exact finite-level centralizers; this replaces capture by the existence of any liftable masa of the relative commutant, which capture supplies but which needs no exact centralizers.
  at-op62-holds-for-representation-lifts: that establishes coordinate capture of the whole commutant for genuine representation lifts; this shows that the block gap only needs a coordinate lift of one maximal abelian subalgebra of the commutant.
  transported-gap-masa-kills-leavitt-hs-models: that uses a masa of the Kazhdan relative commutant pushed by a compressor to kill Leavitt models; this characterizes which finite partitions give a masa of the actor commutant and shows the scalar block gap then comes for free.
  hs-normalization-needs-coarse-actor-scale-pinning: that assumes (H2') as a hypothesis; this reduces (H2') to the existence of a liftable masa of sigma(G)' cap M, and proves that its commutation clause with the aspect-ratio observables holds automatically under (H1).
artifacts:
  - research/artifacts/hs-coarse-gap-aspect-scales-2026-09-12.md
---

**ESTABLISHED.** Let `G` be a group with a finite symmetric generating set `S` and Kazhdan
constant `kappa_S > 0`. Let `sigma_n : G -> U(n)` be a trace-preserving asymptotic
representation, `M = prod_U M_n`, `sigma` the induced homomorphism and
`Q = sigma(G)' cap M`.
- For each `n`, let `{q_(n,A)}_A` be a finite partition of unity by projections of `M_n`,
  with span `C_n`, and put `C = prod_U C_n`.
- For `x in M_n` write `x_A = q_A x q_A` and `tau_A(x) = tau(x)/tau(q_A)`.

1. **Boundary.** `sum_A ||[sigma_n(s), q_(n,A)]||_2^2 -> 0` along `U` for every `s in S` if and
   only if `C <= Q`.
2. **Commutant of a lifted partition.** `C' cap M = prod_U (C_n' cap M_n)`.
3. **Masa gives the gap.** Suppose `C <= Q` is maximal abelian in `Q`. Then for every
   `epsilon > 0`, along `U`, every self-adjoint contraction `x in C_n' cap M_n` satisfies

   ```text
   sum_(s in S) sum_A || [q_A sigma_n(s) q_A, x_A] ||_2^2
       >=  kappa_S^2 sum_A || x_A - tau_A(x_A) q_A ||_2^2  -  epsilon .     (F2)
   ```

4. **Gap gives a masa.** Conversely, if the boundary condition of (1) holds and (F2) holds
   for some `kappa' > 0`, for every `epsilon` along `U`, then `C` is maximal abelian in `Q`.
5. **Commutation clause.** Let `Gamma <= G` be Kazhdan and assume (H1) of
   `hs-normalization-needs-coarse-actor-scale-pinning`, with `A_n = pi_n(Gamma)'`. Under the
   boundary condition of (1), along `U`,

   ```text
   sup { sum_A || [q_(n,A), z_(n,A)] ||_2^2  :  z_(n,A) in Z(A_n), ||z_(n,A)|| <= 1 }  ->  0 .
   ```

   Here the central contractions `z_(n,A)` may depend on the block. In particular
   `sup_(a>0) sum_A ||[q_A, F_a(zeta_A)]||_2^2 -> 0`, where `zeta_A` is the aspect-ratio
   observable and `F_a(x) = x/(x+a)`.

**Reading.**
- (H2') of the conditional assembly, in the consumed form (F2), holds at a generating set
  of vertex generators and strict compressors if and only if `sigma(G)' cap M` has a maximal
  abelian subalgebra that is an ultraproduct of finite partition algebras. Call such a
  subalgebra a liftable masa.
- The gap constant is then the Kazhdan constant of `S`, and the third clause of (H2') is
  automatic. So the actor gap is never the obstacle. The open content of (H2') is lifting
  one masa of the actor's relative commutant to finite partitions.
- Every masa of `Q` contains the center `Z(Q)`. Under (H1), `Q <= prod_U A_n`, and
  `prod_U Z(A_n)` commutes with `prod_U A_n`. So `Z(Q)` contains `Q cap prod_U Z(A_n)`, and a
  liftable masa must lift every almost invariant function of the aspect-ratio profile.

Derivation: `hs-block-gap-liftable-masa-proof`.
