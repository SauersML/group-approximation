---
rg: 2
id: brown-ucp-generator-lift-closes-maslov-gap
kind: route
title: Generator ucp lifts turn a surviving Maslov sector into a forbidden amenable trace
target: maslov-mod3-projective-defect-gap
requires:
  - maslov-sector-tracial-generator-ucp-liftability
  - deligne-twisted-fibres-have-no-amenable-trace
---

Suppose the projective defect gap fails.  The resulting unitary tuples define
a star-homomorphism `Theta:A_alpha -> prod_omega M_(d_n)`.  Apply the required
lifting assertion and write `phi_n(u_s)` for coordinate ucp lifts.  Choose
unitary representatives `U_n(s)` for `Theta(u_s)`.  Then

```text
||phi_n(u_s)-U_n(s)||_(2,d_n) -> 0.                       (BUG1)
```

Since `phi_n` is ucp and `u_s` is unitary, `(BUG1)` makes both Schwarz
defects

```text
I-phi_n(u_s)^*phi_n(u_s),   I-phi_n(u_s)phi_n(u_s)^*
```

tend to zero in tracial 1-norm (indeed in 2-norm after a harmless bounded
estimate).  The ucp Cauchy--Schwarz inequality then shows that `phi_n` is
asymptotically multiplicative in normalized 2-norm whenever one factor is a
canonical generator.  Telescoping over words, and then norm density, gives

```text
||phi_n(ab)-phi_n(a)phi_n(b)||_(2,d_n) -> 0
```

for all `a,b in A_alpha`.  A cluster point of `tr_(d_n) o phi_n` is therefore
an amenable trace by Brown's ucp characterization, contradicting
`deligne-twisted-fibres-have-no-amenable-trace`.

The inverse sector follows from `maslov-inverse-sector-symmetry`.
