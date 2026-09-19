---
rg: 2
id: stw09-quasicentral-corner-quotient-gluing-proof
kind: route
title: Direct-sum a compressed corner model with a quotient model and recover the norm by central support
target: stw09-local-mf-corner-traces-across-qd-extension-force-qd
requires:
  - stw09-jointly-faithful-mf-traces-force-mf
artifacts:
  - research/artifacts/stw09-ix1-separating-mf-traces-audit-2026-08-30.md
---

Write `q:A -> A/I` for the quotient map.  We first prove the norm identity

```text
||x||=max{||q(x)||, lim_n ||p_n x p_n||}.                    (QC1)
```

If `I=0`, the quotient hypothesis already says that `A` is quasidiagonal.
Otherwise discard any initial zero projections, so every corner used below
is nonzero.

Let `z` be the central support projection of `I` in `A**`.  The approximate
unit `(p_n)` converges strongly to the central projection `z`.  The
representation

```text
A/I -> (1-z)A**,             q(x) |-> (1-z)x
```

is faithful: its kernel is `A intersect I**=I`.  Hence
`||q(x)||=||(1-z)x||`.  Moreover `p_n x p_n` converges strongly to `zx`, so
lower semicontinuity of norm gives

```text
||zx|| <= liminf_n ||p_n x p_n||.
```

The reverse inequality holds because `p_n=zp_n` and
`||p_n(zx)p_n||<=||zx||`.  Thus the limit is `||zx||`.  Centrality of `z`
gives `||x||=max{||zx||,||(1-z)x||}`, proving `(QC1)`.

Fix a finite self-adjoint packet `F subset A` containing `1` and an error
`epsilon>0`.  By `(QC1)`, approximate-unit convergence on `I`, and
quasicentrality, choose `n` so that for all requested `x,y in F`,

```text
max{||q(x)||,||p_n x p_n||}>||x||-epsilon,
||[p_n,x]||<epsilon.
```

Choose quasidiagonal u.c.p. models

```text
alpha:p_n A p_n -> M_r,          beta:A/I -> M_s
```

which are sufficiently multiplicative and isometric on the compressed and
quotient packets.  Define the u.c.p. map

```text
Psi:A -> M_r direct_sum M_s,
Psi(x)=alpha(p_n x p_n) direct_sum beta(q(x)).               (QC2)
```

Both summands are unital relative to their target units: compression sends
`1_A` to the unit `p_n` of the corner.  For the corner block,

```text
p_n x y p_n-(p_n x p_n)(p_n y p_n)
 =p_n x(1-p_n)y p_n,
||p_n x(1-p_n)y p_n|| <= ||[p_n,x]|| ||y||.                 (QC3)
```

Thus `(QC3)` plus multiplicativity of `alpha`, and multiplicativity of
`beta` on the quotient block, make `Psi` as multiplicative as desired on
`F`.  Its norm is the maximum of the two block norms.  The isometry estimates
for `alpha,beta` together with `(QC1)` therefore give

```text
||Psi(x)||>||x||-O(epsilon)                  (x in F).
```

Contractivity gives the matching upper bound.  Voiculescu's finite-set
criterion and separability show that `A` is quasidiagonal.

For the tracial corollary, faithfulness of `tau` implies that each
`tau_n` is faithful.  By hypothesis it is an MF trace.  The singleton case
of `stw09-jointly-faithful-mf-traces-force-mf` makes `p_n A p_n` MF: if its
trace model killed `b`, trace convergence would give `tau_n(b* b)=0`, and
faithfulness gives `b=0`.  Each corner is nuclear because it is hereditary
in the nuclear algebra `A`; the Blackadar--Kirchberg nuclear-MF
characterization therefore makes it quasidiagonal.  The quotient is
quasidiagonal by hypothesis, so the first part applies.

**Trust boundary.**  Compression `x |-> p_n x p_n` is not treated as a star
homomorphism; its defect is exactly the transition term in `(QC3)`, and
quasicentrality is what kills that term.  Faithfulness of `tau_n` is used
only for norm detection inside its own corner.  No corner trace is extended
to `A`, no quotient trace is inferred from `tau`, and no exactness, UCT, or
weak-star closure of ambient MF traces is assumed.  Nuclearity is used only
to upgrade the already MF corner algebras to quasidiagonal ones.
