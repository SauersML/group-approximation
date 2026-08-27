---
rg: 2
id: three-line-first-hit-solves-local-morita-edge
kind: claim
title: A three-line first-hit table solves the two local Morita equations at one edge
distinct_from:
  common-oriented-character-table-gives-morita-trace: That gives an abstract sufficient common-table criterion; this constructs the required orientation for one adaptive edge from its stabilized Murray--von Neumann swap.
  free-root-top-boundary-reservoir-is-summable: That partitions characters by polynomial degree; this partitions the three coefficient lines at one adaptive edge.
  finite-schur-head-has-trace-character-escape: That exhibits characters simultaneously detecting all site defects; this isolates the precise spectator-trivial fiber that such escaping characters avoid.
---

**ESTABLISHED LOCAL REDUCTION.**  Work over `F_p`.  At one fixed adaptive edge
write `q=b+a`, where `a<=q`, and let `d` be the new range projection with
`dq=qd=0`.  In the stabilized coefficient ring put

```text
b_0=diag(b,0),       a_0=diag(a,0),       d_0=diag(0,d).
```

They define an elementary-abelian root-table homomorphism

```text
T_0=F_p^3 -> <x_ij(b_0),x_ij(a_0),x_ij(d_0)>.         (TLF1)
```

The map is allowed to have a kernel in a particular representation; the
corresponding Fourier atoms below are then simply zero.

The explicit Murray--von Neumann involution fixes `b_0` and swaps `a_0`
with `d_0`.  Hence its stabilized Steinberg word normalizes `T` by

```text
(u,v,w) -> (u,w,v).                                   (TLF2)
```

For the Fourier PVM of `T_0`, identify a character with its coordinate triple
`(u,v,w) in F_p^3`.  Define the oriented sets

```text
Omega_q ={(u,v,w):(u,v)!=(0,0)},
Omega_d ={(0,0,w):w!=0},
Omega_a ={(0,v,0):v!=0},
Omega_(q+d)=Omega_q disjoint_union Omega_d.           (TLF3)
```

Then the swap `(TLF2)` carries `Omega_a` exactly onto `Omega_d`, while the
last identity in `(TLF3)` is a literal disjoint union.  Thus, for the masses
of these common-PVM subsets,

```text
mu(a)=mu(d),
mu(q+d)=mu(q)+mu(d).                                  (TLF4)
```

The same conclusions hold with dimension-independent `o(1)` error in an HS
microstate once this fixed finite root table and its normalizer word are
exactified.

Consequently the analogues of `(MTA1)` and `(MTA2)` require no further
decoder at this one edge.  One remaining local assertion is the
**conditioned-source estimate**

```text
tr(P_(Omega_a)) >= tr(Q_sigma P_i)-o(1).               (TLF5)
```

Here `P_(Omega_a)` is not the full nontrivial spectral support of the source
root: it is the part on which both spectator coordinates `b_0` and `d_0`
are trivial.  Neither Steinberg conjugacy nor coefficient orthogonality
implies `(TLF5)`.  An arbitrary exact representation may put all
`a_0`-nontrivial character mass in fibers with `u!=0` or `w!=0`.

Thus every edgewise Morita construction must force selected BCS mass into
the double-spectator-trivial first-hit fiber, with failure charged to
presentation energy.  This is not yet the global decoder.  Different
outgoing edges can give different sets `Omega_q`, hence different candidate
masses for the same parent `q`.  Besides `(TLF5)`, a complete construction
must orient all edge tables inside one common PVM so that the parent subset
is independent of the chosen forbidden type.  That is exactly the
common-table compatibility required by
`common-oriented-character-table-gives-morita-trace`.

The estimate does not follow from the local table itself.
`three-line-first-hit-has-invariant-spectator-escape` gives an exact
one-dimensional normalizer representation supported on a character which is
simultaneously nontrivial on the source and destination lines.  It sees the
source root fully but gives zero mass to `Omega_a`.
