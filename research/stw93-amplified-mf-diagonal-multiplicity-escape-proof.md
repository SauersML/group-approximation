---
rg: 2
id: stw93-amplified-mf-diagonal-multiplicity-escape-proof
kind: route
title: Dilute one multiplicity block in an amplified faithful MF embedding
target: stw93-faithful-full-diagonal-retains-norm-kernel
requires: []
artifacts:
  - research/artifacts/stw93-faithful-diagonal-multiplicity-escape-audit-2026-08-30.md
---

Choose a unital faithful MF embedding

```text
phi:A -> product_omega M_(r_k).
```

Let `m_k->infinity` along `omega`.  Tensoring representatives by the
identity defines a unital homomorphism

```text
Phi:A -> M=product_omega M_(r_k m_k),
Phi(a)=[(a_k tensor 1_(m_k))] whenever phi(a)=[(a_k)]. (1)
```

This is well defined because tensoring by an identity preserves operator
norm, and it is faithful for the same reason.  The normalized matrix trace
of `M` is the ultralimit of the coordinate normalized traces (and is the
unique normalized trace by dimension-independent matrix Dixmier averaging).
Its pullback along `Phi` is a normalized trace on `A`; monotraciality
therefore makes that pullback `tau`.  In particular it is faithful, so
`Phi` is a faithful trace-preserving diagonal.  The GNS representation of
the pullback trace is exactly the original tracial GNS representation of
`A`; coordinate amplification therefore changes none of its von Neumann
spectral-gap inequalities.

Put

```text
p=[(1_(r_k) tensor e_11)] in M.                         (2)
```

Every representative in `(2)` commutes exactly with every representative
in `(1)`, so `p in D=M intersect Phi(A)'`.  Also

```text
||p||=1,                 tau_M(p)=lim_omega 1/m_k=0.    (3)
```

Thus `p` is a nonzero projection in `J_tau intersect D`.  A tracial
spectral-gap estimate sees `(2)` only as the zero `L^2` vector, since
`||p||_2^2=tau_M(p)=0`; it gives no operator-norm information about `p`.

For each fixed `n`, discard an `omega`-small set so that `m_k>=n`, and set

```text
p_j=[(1_(r_k) tensor e_jj)],
v_j=[(1_(r_k) tensor e_j1)],       1<=j<=n.             (4)
```

All these elements commute with `Phi(A)`.  The `p_j` are pairwise
orthogonal and the `v_j` prove `p_j` Murray--von Neumann equivalent to `p`.
If `q` is a normalized trace on `D`, then

```text
n q(p)=q(sum_(j=1)^n p_j)<=q(1)=1.                     (5)
```

As `(5)` holds for every `n`, `q(p)=0`.  Thus every bounded tracial
functional annihilates `p` (decompose it into linear combinations of
positive tracial functionals).  The Cuntz--Pedersen annihilator theorem,
which identifies `Com_sa(D)` with the common kernel of bounded traces on
`D_sa`, now gives `p in Com_sa(D)`.

For the XCIII algebra, use the known MF embedding of `C*_r(F_2)` and the
nuclear quasidiagonal model of `Z` to obtain an MF embedding of their
minimal tensor product.  Its unique trace is faithful, while its GNS
algebra is `L(F_2) tensor_bar R`; the standard adjoint spectral gap on the
first tensor factor is unchanged by `(1)`.  Hence the construction retains
the faithful diagonal and the exact full-factor spectral-gap datum while
exhibiting the norm/`2`-norm separation claimed above.
