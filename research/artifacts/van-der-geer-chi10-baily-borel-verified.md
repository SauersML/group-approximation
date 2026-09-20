# Verified quotes: van der Geer, *Siegel modular forms and their applications* (arXiv:math/0605346)

Source: https://arxiv.org/pdf/math/0605346, downloaded 2026-09-19 by swarm-0917-w19-w19-deligne-break.
Text was extracted with pypdf, and the quotes below are copied from that extraction. Line breaks and hyphenation
artefacts are normalised; wording and formulas are unchanged.

## (Q1) Igusa's cusp form chi_10 (Section 10, "Examples of cusp forms", p. 28-29)

> For g = 2 there is a similar cusp form chi_10 of weight 10 with development
> chi_10 ( (tau_1 z ; z tau_2) ) = ((exp 2 pi i tau_1) exp(2 pi i tau_2) + ... )(pi z)^2 + ...
> which vanishes (with multiplicity 2) along the 'diagonal' z = 0. So its zero divisor in A_2 is the divisor of
> abelian surfaces that are products of elliptic curves with multiplicity 2.

## (Q2) Baily-Borel (Section 11, p. 23)

> Theorem 11.1. Scalar Siegel modular forms of an appropriately high weight define an embedding of
> Gamma_g \ H_g^* into projective space and the image of Gamma_g \ H_g (resp. Gamma_g \ H_g^*) is a
> quasi-projective (resp. a projective) variety.

In the same section, the Satake boundary of `Gamma_2 \ H_2^*` is `Gamma_1 \ H_1 u Gamma_0 \ H_0`. It has
dimension 1 in a threefold.

## How these are used

In `mod-s2-holomorphic-torelli-certificates-unbounded-mass-proof`:
- (Q1) gives `C . H_1 = 5 deg(lambda|C)` for compact curves `C` in `A_2(Gamma')`.
- (Q2) gives positivity and bounded families of curves of bounded `lambda`-degree.
