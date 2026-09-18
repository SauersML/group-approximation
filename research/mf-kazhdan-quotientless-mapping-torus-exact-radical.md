---
rg: 2
id: mf-kazhdan-quotientless-mapping-torus-exact-radical
kind: claim
title: Some MF Kazhdan group without finite quotients has a mapping torus whose MF radical is the whole kernel
distinct_from:
  mapping-torus-mf-radical-descends-through-kernel-radical: That is the reduction which isolates this problem; this is the remaining existence question for the extrinsic case.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: That asks for a torsion-free sofic kernel with a compression defect; this asks only for the purely extrinsic radical, with no soficity, torsion-freeness or finite presentation.
  mf-not-closed-under-integer-extensions: That records a non-MF integer extension of an MF group; this needs the radical to be the entire Kazhdan kernel.
  lef-kazhdan-group-without-finite-quotients-exists: That supplies candidate kernels; this asks whether one of them has an automorphism of the required kind.
  finite-outer-order-mapping-torus-is-virtually-product: That excludes finite outer order; this needs an infinite-order outer automorphism.
  matricial-compression-ring-exists: That is a ring existence problem which implies this one with Q = EL_4(R); this is the group statement, which could also be witnessed by non-elementary kernels.
---

There exist a nontrivial countable group `Q` and `psi in Aut(Q)` such that

```text
Q has property (T), Q is MF, Q has no nontrivial finite quotient,
Rad_MF(Q semidirectProduct_psi Z) = Q x {0}.            (XMF)
```

Any such `psi` has infinite order in `Out(Q)`, by
`finite-outer-order-mapping-torus-is-virtually-product`.

**Why it matters.**  By `mapping-torus-mf-radical-descends-through-kernel-radical`,
every witness `(G,K)` of `torsion-free-sofic-exact-mf-radical-over-z` either
has an intrinsically full-radical kernel, `Rad_MF(K) = K`, or yields `(XMF)`
with `Q = K/Rad_MF(K)`.  So if `(XMF)` is false, the extrinsic route adds
nothing: the flagship then needs a torsion-free sofic Kazhdan kernel with
`Rad_MF(K) = K`, and the automorphism is irrelevant to the radical.

## Attempts

1. **Periodization of corona almost-representations (2026-09-17, dead).**
   Idea: from almost-representations `rho_n` of `Q`, build
   `Sigma = (+)_{i in Z/N} rho_n o psi^{j+i}` on `C^d (x) l^2(Z/N)`, and let
   the generator of `Z` act by the cyclic shift twisted by a unitary `U` at the
   wrap.
   - *What works.*  Property (T) makes each slot uniformly nontrivial, because
     the Kazhdan constant for `S u psi(S) u ...` is controlled by the pair
     `(S,eps)` transported by `psi^m`.  An Ozawa sum-of-squares certificate
     transports under `psi^m` without growth in word length.
   - *Where it dies.*  The wrap needs
     `rho_n o psi^j ~ Ad(U) o rho_n o psi^{j'}` on generators, to operator-norm
     accuracy `eps`.  Pigeonhole over the `eps`-net of `U(d)^S` gives this only
     after `J ~ (C/eps)^{|S| d^2}` iterates.  So `rho_n` must be accurate on
     balls of radius `lambda^J`, where `lambda` is the growth of `psi` on `S`.
     But `d` grows with that radius, and the recurrence time grows with `d`.
     The wrap block carries operator-norm weight `1`.  In the Hilbert--Schmidt
     setting it has weight `1/N` and the construction closes, which is the
     amenable-extension permanence.  The corona norm sees it fully.  So
     periodization cannot prove MF for these mapping tori, and it cannot
     certify `(XMF)` either: there is no step at which it detects non-MF.
2. **Tracial obstructions cannot see (XMF) (2026-09-17, remark).**  Any
   obstruction carried by an invariant trace or measure on `Q` persists to
   `Q semidirectProduct_psi Z`, by Markov--Kakutani averaging on the compact
   convex set of traces.  So an extrinsic defect must be invisible to every
   tracial invariant.  This matches the sofic case, where hyperlinearity holds
   throughout.
3. **Compression recipe gate (2026-09-17, open).**  The known non-MF mechanism
   (`normal-kazhdan-defect-non-mf`) would give `(XMF)` from a Kazhdan
   `L <= Q x {0}` (the degree is forced, by the forced-degree remark of the
   descent node), an element `t` of nonzero degree with `t L t^{-1} <= L`
   properly, and a root `c` commuting with `L` whose transported defect
   `[t c t^{-1}, L]` normally generates `Q` inside the mapping torus.  No
   candidate `(Q,psi)` carrying these data is known.
4. **Ring-theoretic instantiation of the recipe (2026-09-17, group-rings).**
   `simple-ring-centralizer-compression-gives-xmf` (established) proves that
   the gate of Attempt 3 is met by `E = EL_3(S) semidirectProduct_sigma Z`
   whenever:
   - `S` is a finitely generated, infinite, simple ring and `EL_3(S)` is MF;
   - `sigma(R) <= R` for a finitely generated subring `R`;
   - some `z in [S^x,S^x]` commutes with `R` but not with `sigma^{-1}(R)`.

   The pieces:
   - The source is `L = EL_3(R)`, Kazhdan by Ershov--Jaikin--Kassabov.
   - The root is the scalar `zI`, which lies in `EL_3(S)` by the Whitehead
     lemma.
   - The transported defect contains a nonzero `x_12(r)`.  By the Steinberg
     relations and simplicity it normally generates `EL_3(S)`, which then
     has no finite quotients.

   So `(XMF)` now reduces to the ring gate
   `simple-ring-with-centralizer-compressing-automorphism`, recorded as the
   route `xmf-via-simple-ring-centralizer-compression`.  That node records
   the obstruction: no automorphism implemented in a locally matricial
   overring works, because finite dimension forces the compression to be an
   equality.  Kernels built this way contain Weyl torsion, so they serve
   `(XMF)`, the quotient `Q`, and never the torsion-free flagship kernel
   directly.
5. **Matricial compression ring recipe (2026-09-17, group-rings, open).**
   `xmf-via-matricial-compression-ring-proof` proves `(XMF)` from a ring
   problem, `matricial-compression-ring-exists`.  It needs:
   - (R1) a finitely generated, exactly matricial ring `R`;
   - (R2) an automorphism `psi` of `R`;
   - (R3) a finitely generated subring `R_0` with `psi(R_0) <= R_0`;
   - (R4) a unit `z` centralizing `R_0`;
   - (R5) the ideal generated by `psi(z) p psi(z)^(-1) - p`, over `p in R_0`,
     is `R`.

   The witness is `Q = EL_4(R)`.  The source is `EL_3(R_0)` in the upper-left
   block, and the root is `c = diag(z,z,z,z^(-3))`, which lies in `EL_4` by
   Whitehead.  Elementary commutator calculus puts `Q` inside the defect normal
   subgroup.  `normal-kazhdan-defect-non-mf` then gives `Rad = Q`, and the
   finite-residual bound gives no finite quotients.

   The obstruction side is `matricial-rings-rigidify-compression-centralizers`.
   Conjugation cannot shrink a finite-dimensional subalgebra, so no unit of
   any exactly matricial overring implements `psi` on `R_0 u {z}`.  Hence the
   skew Laurent ring `R[t^(+-1); psi]` must be non-matricial.  This kills:
   - inner and residually-finite-action compressors;
   - finite-order `psi`;
   - group rings (augmentation);
   - crossed products whose `R_0` contains all of `u_Gamma` for ICC `Gamma`;
   - the monomial subrings of the minimal-subshift ring under subshift
     automorphisms.

   No surviving ring is known.
6. **Stably finite certificates (2026-09-18, operator-algebras, dead class).**
   `kazhdan-mapping-tori-have-proper-stably-finite-radical` (established)
   proves that for every nontrivial MF Kazhdan `Q` and every `psi`, some
   homomorphism `Q semidirectProduct_psi Z -> U(P)`, with `P` a finite von
   Neumann algebra, is nontrivial on `Q`, with Kazhdan-constant defect at least
   `kappa^2`.  So `Rad_sf(G)` is a proper subgroup of `Q x {0}`.
   - *What dies.*  Any certificate valid in all stably finite targets:
     Dedekind-finiteness identities `t p_L t^* = p_L`, infiniteness of
     `C*_max`, K_0 and projection compression, and tracial obstructions.
   - *Invariant.*  The normalized trace of the set where `t q t^-1 = psi(q)`
     fails.
   - *Death step.*  Evaluation at the Folner model `sigma_N`: the relation
     fails on one wrap block of trace `1/N`, while the Kazhdan bound holds on
     every block.
   - *What survives.*  Norm-model arguments over the whole group, as in
     Attempts 3--5.  This is the same wrap block where Attempt 1 dies.
