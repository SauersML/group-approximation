---
rg: 2
id: algebraic-bcs-corner-has-relator-energy-decoder
kind: claim
title: An algebraic non-CE BCS corner automatically has a finite ordinary-relator energy decoder
distinct_from:
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that pulls back the canonical corner trace qualitatively; this gives the finite-coordinate normalized-HS payment and shows that no additional analytic decoder is needed after the algebraic corner map exists.
  oracular-2csp-algebraic-corner-map-is-a-canonical-groupifier: that gives the ultraproduct decoder for arbitrary finite oracular games; this extracts a fixed finite relator menu and a dimension-independent quantitative defect floor for the fixed non-CE BCS.
  embedded-packet-projection-has-no-relator-ideal-certificate: that forbids paying a nonzero embedded packet projection itself; this pays the BCS relation residuals, which are zero algebraically in the corner, conditional on retaining positive corner mass.
---

**ESTABLISHED CONDITIONAL PAYMENT.**  Let `B` be the fixed finite BCS algebra
with no Connes-embeddable tracial state, and let

```text
Phi:B -> q C[Gamma] q,              Phi(1)=q!=0          (ARC1)
```

be a unital star homomorphism, where `q=q*=q^2` and every `Phi(X_x)` has
finite group support.  Fix any presentation `Gamma=<S|R>` containing those
supports.  Then there are a finite subset `R_0 subset R`, constants
`C,epsilon_0>0`, and a dimension-independent decoding procedure with the
following property.

For every unitary `S`-tuple `U`, put

```text
epsilon(U)^2=sum_(r in R_0)||r(U)-I||_2^2.              (ARC2)
```

If `epsilon(U)<=epsilon_0`, spectral rounding of `q(U)` gives a projection
`Q`, and whenever

```text
tau(Q)>=a>0,                                             (ARC3)
```

the compressed coefficient tuple can be reflection-rounded on `Q C^d` to
unitaries `Z_x` satisfying

```text
E_B(Z)<=C epsilon(U)^2/a.                               (ARC4)
```

Here `E_B` is the normalized-corner version of the fixed robust BCS energy in
`non-ce-bcs-has-robust-approximate-energy-gap`.  Therefore

```text
epsilon(U)^2 >= a beta_B^rob/C.                         (ARC5)
```

Thus positive canonical corner density converts the fixed non-CE BCS energy
directly into ordinary-word normalized-HS relator energy.  For canonical
microstates, `(ARC3)` is automatic with, say,
`a=tau_Gamma(q)/2`, because the canonical trace is faithful on `C[Gamma]`.

The exact algebraic corner map is load-bearing.  A merely positive
group-algebra energy or a nonzero finite-packet projection has no such
certificate: evaluating a proposed upper bound by relator defects in the
left regular representation gives zero on the right and a positive value on
the left.  Hence finite central sectors do not create canonical-trace
promotion by positivity alone.  They succeed precisely after all BCS corner
relations, especially cross-context marginal equality, hold as algebraic
identities.  Constructing that compatible atlas remains
`signed-hecke-compatible-projection-atlas-for-nonce-bcs`; ordinary-word HS
payment is not an additional hole beyond it.

