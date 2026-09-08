---
rg: 2
id: noncentral-frobenius-negative-corner-is-rational-matrix-algebra
kind: claim
title: A noncentral translation involution has a full rational matrix corner of every power-of-two size
distinct_from:
  affine-frobenius-group-has-almost-full-simple-block: that uses the augmentation complement of an odd prime translation group; this uses exactly the negative projection of one noncentral involution in characteristic two.
  monomial-central-sign-has-types-or-affine-returns: that analyzes central-sign selector packets and outer multiplicity gauges; this constructs the whole negative corner of a noncentral involution and classifies its literal unitary and partial-isometry transports.
artifacts:
  - research/artifacts/noncentral-frobenius-negative-rational-matrix-corner-2026-09-08.md
---

Let `k=F_(2^n)` with `n>=1`, let
`F=k_add semidirect k^times`, and write `t_v,m_s` for its
translations and multipliers. Put

```text
J=t_1,
q=(1-J)/2,
Omega={a in k:Tr_(k/F2)(a)=1},
p_a=2^(-n) sum_(v in k) (-1)^Tr(av) t_v.
```

Then the rational elements

```text
E_ab=p_a m_(b/a) p_b          (a,b in Omega)
```

are a basis of matrix units for the entire corner:

```text
q Q[F] q ~= M_(2^(n-1))(Q),
sum_(a in Omega) E_aa=q.
```

The normalized canonical corner trace is the normalized matrix
trace. No additional finite-type projection is selected. For `n>=2`,
`J` is noncentral; the case `n=2` is the full negative
double-transposition corner of `A_4`, isomorphic to `M_2(Q)`.

The packet group elements preserving `q` are exactly the
translations, and their compressions act diagonally by
`(-1)^Tr(av)`. For a multiplier `s!=1`, the literal compression
`q m_s q` is instead a partial isometry whose initial and final
projections both have half the matrix rank of `q`.

This supplies exact finite-support realizations of local matrix
PVMs and an involution authenticated by the full corner unit.
It does not construct the shared variable images or the
cross-context identities of `B_loop`; those cannot all remain
inside this one finite-dimensional algebra.

DERIVATION
noncentral-frobenius-fourier-matrix-unit-proof
