---
rg: 2
id: native-relator-soft-modes-persist-in-simple-ideal-blocks
kind: claim
title: Native relator soft modes persist inside irreducible full-ideal matrix blocks
distinct_from:
  km-triangle-relative-gap-failure-has-fd-full-support-witnesses: that gives finite-dimensional packets whose central ideal support is one; this removes every direct-sum and central-support dilution by selecting one irreducible simple matrix block.
  finite-packet-triangle-repair-is-ideal-block-choi-feasibility: that identifies the exact affine Choi intersection inside an arbitrary finite-dimensional ideal block; this proves that even when that block is the whole simple matrix algebra, no fixed native reservoir has a support-based spectral angle.
  overlap-and-kernel-floors-do-not-exclude-splitting: that shows local face and Gram geometry cannot decide splitting after adding a non-RFD quotient summand; this stays inside genuine finite-dimensional representations of the actual RFD ambient algebra and uses the native relator ideal.
---

**ESTABLISHED (irreducible native soft modes).**  In the actual Kac--Moody
triangle, fix a finite subset `F subset G_0`, a finite native relator
reservoir `B_W` as in `(FDR4)`, and `eta>0`.  There are an **irreducible**
finite-dimensional representation

```text
rho:G_0->U(d)
```

and a unit vector `xi in C^d` such that

```text
rho(I)=M_d,
sum_(g in F)||rho(g)xi-xi||^2
 +sum_(x in B_W)||rho(x)xi||^2<eta.                        (NSB1)
```

In particular the central ideal support is not merely nonzero but

```text
z_rho=1_(M_d),       rho(I)=M_d,                           (NSB2)
```

while the native finite-reservoir Laplacian has arbitrarily small Rayleigh
quotient.

Consequently there is no constant `c_W>0`, even after restricting to
irreducible full-ideal-support packets, for an estimate of the form

```text
sum_(x in B_W)||rho(x)xi||^2
   >=c_W ||z_rho xi||^2.                                  (NSB3)
```

Thus RFD plus maximal native-ideal support does not give a metric angle or
Poincare inverse for a fixed relator reservoir.  Any theorem deciding the
middle Choi region must use the **specific Choi correction direction and
positivity constraints**, not only the support projection of `rho(I)` or the
fact that the ideal image is a full matrix algebra.

**Scope.**  `(NSB1)` does not show that the affine Choi slice is empty or
nonempty.  Low relator energy occurs on both sides of the lift-versus-separator
dichotomy.  It is a quantitative obstruction to a support-only
transversality proof, now without the loophole that small energy came from a
trivial quotient summand, a small central ideal block, or mixing among
irreducible summands.

Proof: `select-one-irreducible-summand-from-the-full-support-soft-packet`.

DERIVATION
select-one-irreducible-summand-from-the-full-support-soft-packet
