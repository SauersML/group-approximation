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
