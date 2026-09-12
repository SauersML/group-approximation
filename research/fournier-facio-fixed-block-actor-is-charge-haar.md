---
rg: 2
id: fournier-facio-fixed-block-actor-is-charge-haar
kind: claim
title: The positive fixed-block actor has Haar spectrum and wandering columns
invalidates:
  - fournier-facio-biased-dense-spectrum-block-witness
  - fournier-facio-irrational-scalar-fixed-block-witness
distinct_from:
  fournier-facio-fixed-block-spectrum-escapes: That proves every finite spectral cutoff is null; this identifies the complete aggregate spectral law on the positive fixed sector.
  fournier-facio-dimension-at-infinity-escape-is-sharp: That gives a one-generator calibration attaining the law; this proves the law is forced in every common-block Fournier--Facio witness.
  fournier-facio-bounded-block-near-witness-impossible: That uses one adaptively selected recurrent power; this simultaneously computes every fixed Fourier moment.
---

**ESTABLISHED HAAR-MOMENT LAW.**  In the notation and on the positive
fixed-block sector furnished by
`fournier-facio-fixed-block-spectrum-escapes`, let

```text
F=union_{y in F_g} X_y,
P_F=projection onto ell^2(F),
U=P_F B_g P_F,
psi(A)=phi_mu(P_F A P_F)/mu(F).                         (FFHM1)
```

Because `B_g` preserves every block in `F_g`, `U` is a unitary in the
corner.  Its charged spectral distribution is exactly Haar measure on the
circle:

```text
psi(U^n)=0                     for every n in Z\{0}.     (FFHM2)
```

The underlying statement is pointwise stronger.  For every `n!=0` and
`epsilon>0`,

```text
mu({x in F: |<U^n delta_x,delta_x>|>=epsilon})=0.       (FFHM3)
```

Equivalently, every fixed Krylov window is orthonormal in charge.  For each
finite `N` and `epsilon>0`,

```text
mu({x in F : max_{0<=i<j<=N}
       |<U^i delta_x,U^j delta_x>|>=epsilon})=0.         (FFHM4)
```

This follows from `(FFHM3)` because the displayed inner product is the
`(j-i)`-th return coefficient and only finitely many differences occur.

Indeed charged near multiplicativity gives `B_g^n=B_(g^n)` in the charged
column quotient.  The group is torsion-free, so `g^n!=1`, and essential
freeness makes the diagonal coefficient of `B_(g^n)` vanish in charge.
Compression to `F` preserves this equality because `P_F` commutes with
`B_g`.  Negative moments follow by adjoints.  The trigonometric polynomials
are dense in `C(T)`, so `(FFHM2)` uniquely identifies the spectral measure as
normalized Lebesgue measure.

This rules out more than bounded spectral support.  A dense finite spectrum
with any fixed Fourier bias, a slowly varying irrational phase with a
nonzero limiting moment, or a large amplification of a non-Haar phase law
cannot carry the fixed sector.  Even scalar phases distributed exactly by
Haar measure fail `(FFHM3)`, because their diagonal coefficients have modulus
one.  The remaining internal model must assemble finite spectra whose
**charged aggregate law is Haar at every fixed moment**, whose powers move
charged basis columns off themselves, and which retain enough noncommutative
coupling to satisfy all other Fournier--Facio relations.

The constraint is sharp for one actor.  In
`fournier-facio-dimension-at-infinity-escape-is-sharp`, the signed-square
block-cycle unitary has finite cyclic spectra on every block, block lengths
escape to infinity in charge, and every nonzero charged moment vanishes.
Thus a Haar marginal alone is not an obstruction; the unresolved content is
its simultaneous coupling to the other generators and the two compression
relations.

Proof: `fournier-facio-fixed-block-haar-moment-proof`.
