---
rg: 2
id: noncompact-right-holonomy-is-not-compact-profinite
kind: claim
title: Noncompact lattice holonomy is not an inner perturbation of compact profinite translation
distinct_from:
  dense-s-arithmetic-translation-algebra-is-amplified-profinite: that identifies the stable base and the right lattice action; this proves that its nontrivial holonomies cannot be replaced, even up to inner cocycle, by the compact right translations visible in the canonical profinite models.
  homogeneous-k-orbit-factor-has-no-finite-a-refinement: that excludes a finite Cartan factor retaining the spherical label; this excludes a different non-Cartan shortcut, namely absorbing lattice returns into the exactly modeled compact right-translation action.
  iwahori-index-data-does-not-block-ultraproduct-gluing: that reduces the residual to global holonomy after local index-three alignment; this proves that the most natural profinite implementation represents the wrong outer automorphism classes.
---

**THEOREM (established here; proof in
`right-translation-outer-class-injectivity-proof`).**  Put

```text
L=SL_2(Q_2),                 A=SL_2(Z[1/2]),
P=L^infinity(L) rtimes A,
alpha_h(f)(x)=f(xh) and alpha_h(u_a)=u_a.                (NCH1)
```

Then the right-translation map is injective modulo the center:

```text
alpha_h is inner in P    iff    h is in Z(L)={+-I}.       (NCH2)
```

More generally,

```text
alpha_h alpha_k^(-1) is inner    iff    hk^(-1) in Z(L)  (NCH3)
```

up to the harmless reversal coming from the right-action convention.

Let `Lambda'<L` be the torsion-free cocompact lattice of the homogeneous
quotient construction.  Since `Lambda' cap K={e}` for the compact subgroup
`K=SL_2(Z_2)`, every `lambda in Lambda'\{e}` and every `k in K` satisfy

```text
[alpha_lambda] != [alpha_k]  in Out(P).                  (NCH4)
```

Consequently the global cycle returns left after the local index-three
alignment cannot be implemented by replacing them with compact right
translations of `K`, even after allowing arbitrary inner cocycle corrections
inside `P`.  The canonical congruence models of
`N=L^infinity(K) rtimes SL_2(Z)` implement every compact `alpha_k` exactly on
finite quotients `K/K_m`; `(NCH4)` proves that this exact profinite
implementation is the wrong outer class for every nontrivial lattice
holonomy.

**Scope.**  This is not an obstruction to weak innerness after a specially
chosen embedding `P->R^omega`.  An outer automorphism of `P` may become
spatial in a larger ultrapower.  It rules out the concrete shortcut of using
the existing compact right-regular permutations (or the right-translation
coaction) as the required lattice implementers.  A positive construction must
model the genuinely noncompact return germs simultaneously.

DERIVATION
right-translation-outer-class-injectivity-proof
