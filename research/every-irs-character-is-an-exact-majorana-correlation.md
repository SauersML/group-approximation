---
rg: 2
id: every-irs-character-is-an-exact-majorana-correlation
kind: claim
title: Every IRS character is one exact Majorana commutator correlation in a single Clifford crossed product
distinct_from:
  random-coset-lamp-correlations-realize-every-irs-character: that uses a measurable direct integral of subgroup-dependent wreath group factors; this consolidates the whole IRS into one separable orthogonal representation and one hyperfinite Clifford base.
  gaussian-action-haar-algebraic-factor-criterion: that classifies when a Gaussian action is a factor of compact-abelian Haar; this gives an exact bounded correlation in the fermionic second quantization for every orthogonal representation.
  kun-thom-clifford-crossed-product-ce: that asks for Connes embeddability of a specific arithmetic coset Clifford action; this constructs the Clifford action canonically from an arbitrary IRS character but makes no embeddability assertion.
---

Let `mu` be an IRS of a countable group `Gamma` and

```text
phi_mu(g)=mu({H:g in H}).                                (IMC1)
```

There is a separable real orthogonal representation `pi_mu` with a unit
vector `xi` such that

```text
<xi,pi_mu(g)xi>=phi_mu(g).                               (IMC2)
```

Concretely, take the direct integral of the quasi-regular representations
`ell^2(Gamma/H)` and the measurable unit field `delta_H` at the base coset.

Let `R_Cl` be the tracial Clifford von Neumann algebra of this real Hilbert
space, with Majorana operators `c(v)` satisfying

```text
c(v)c(w)+c(w)c(v)=2<v,w>,
tau_Cl(c(v)c(w))=<v,w>.                                  (IMC3)
```

Orthogonal second quantization gives the Bogoliubov action
`alpha_g(c(v))=c(pi_mu(g)v)`.  In the crossed product

```text
M_mu=R_Cl crossed_product_(alpha) Gamma                  (IMC4)
```

with canonical actor unitaries `U_g`, the single involution `C=c(xi)` obeys

```text
tau_(M_mu)(C U_g C U_g^*)=phi_mu(g)                      (IMC5)
```

for every `g`.  This is an exact bounded encoding in one separable finite
von Neumann algebra; it removes the varying wreath fibers from the lamp
construction.

It still does not promote the IRS trace.  The honest actor copy has
`tau(U_g)=delta_(g,e)`, and

```text
V_g=C U_g C U_g^*=c(xi)c(pi_mu(g)xi)                     (IMC6)
```

is not multiplicative in general.  Conjugating `U_g` by the fixed `C` would
give a multiplicative copy, but its canonical trace remains regular.  Thus
fermionic second quantization gives the optimal local correlation without a
trace-preserving representation of the IRS GNS algebra.

