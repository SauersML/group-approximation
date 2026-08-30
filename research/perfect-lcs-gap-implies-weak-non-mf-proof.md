---
rg: 2
id: perfect-lcs-gap-implies-weak-non-mf-proof
kind: route
title: Renormalize the finite central sign sector of a hypothetical weak MF model
target: perfect-lcs-gap-implies-weak-non-mf
requires:
  - mf-finite-normal-tracially-visible
artifacts:
  - research/artifacts/property-t-free-non-mf-literature-audit-2026-08-30.md
---

Let `Gamma=Gamma(A,b)` and write `J` for its distinguished central
involution.  The Cleve--Liu--Slofstra solution-group criterion (equivalently
Paddock--Slofstra, Lemma 5.7(1)) gives

```text
omega^co(G(A,b))=1  =>  J!=1 in Gamma.                         (LNM1)
```

Thus `K=<J>~C_2` is a nontrivial finite normal subgroup of `Gamma`.

Assume for contradiction that `Gamma` is weak MF.  Apply
`mf-finite-normal-tracially-visible` to `K` and `J`.  It gives
operator-norm local models `v_n` of `Gamma` whose operator-norm
multiplication defects tend to zero and for which

```text
limsup_n Re tr(v_n(J)) <= 1-c                              (LNM2)
```

for a fixed `c>0`.  In particular

```text
liminf_n ||v_n(J)-1||_2^2 >= 2c.                           (LNM3)
```

The construction behind that established theorem is worth recording here
because it is the norm firewall.  In a faithful norm-corona model, restrict
the finite group representation on `<J>` to a nonzero isotypic projection
which sees `J`, sum its finite `Gamma`-orbit to obtain an invariant
projection, lift that projection to matrix projections, and polar-correct
the compressed lifts.  Operator-norm defects do not increase under
compression.  The compressed matrices are normalized by the rank of the
corner itself, so `(LNM2)` remains uniform even if the original sign sector
has vanishing relative rank.  No implication from weak MF to hyperlinearity
is being assumed.

Since normalized Hilbert--Schmidt norm is bounded by operator norm, the
`v_n` are normalized-Hilbert--Schmidt approximate representations of
`Gamma`, and `(LNM3)` makes `J` nontrivial in approximate representations.
Slofstra--Vidick, Proposition 4.3 / Corollary 5.3 (also
Paddock--Slofstra, Lemma 5.7(2)), then gives

```text
omega^q(G(A,b))=1,                                         (LNM4)
```

contrary to the hypothesis.  Hence `Gamma(A,b)` is not weak MF.

Every step in this route is finite-group character theory, projection
lifting, matrix-corner compression, polar decomposition, or the standard
LCS solution-group correspondence.  Property `(T)` and all Kazhdan
machinery are absent from the proof cone.  End proof.
