---
rg: 2
id: predicate-preserving-nonscalar-frames-miss-forbidden-source
kind: claim
title: Predicate-preserving nonscalar carrier frames retain a forbidden common kernel
distinct_from:
  scalar-bus-packet-couplings-retain-all-global-assignments: that glues local irreducible sectors through scalar edge restrictions; this permits genuinely nonscalar selected-type projections and arbitrary partial-swap transports, but proves their transported carrier frame still misses the same forbidden source atom when the transports preserve predicate semantics
  range-local-finite-edge-authentication-is-affine: that derives affine support and a canonical-trace leakage floor from one finite edge subgroup; this requires no finite edge group or Bass--Serre model and applies to any finite family of selector-equivariant partial isometries or conjugate carrier projections
  tensor-context-types-classicalize-common-source: that aligns complete context algebras and thereby forces all pulled-back contexts to commute; this allows the contexts to remain noncommuting and rules out only the smaller nonscalar-frame repair of CPS9
  single-finite-type-promotion-forces-a-finite-perfect-strategy: that assumes one type-preserving tensor factorization saturates the full common source; this proves that finite collections of transported copies cannot create that saturation in the first place
---

**ESTABLISHED.**  Let `A` be a finite Boolean selector algebra acting on a
Hilbert space, with character projections `(p_a)_(a in A^)`.  Fix a proper
allowed set `R subsetneq A^` and write

```text
p_R=sum_(a in R) p_a,       F=Q(1-p_R),                (PNF1)
```

where `Q` is a nonzero projection commuting with `A`.  Assume `F!=0`.

For `1<=i<=N`, let `S_i` be a partial isometry with common initial
projection `S_i^*S_i=Q`.  Let `A_i` be a copy of the selector algebra on its
range, let `phi_i:A->A_i` be an isomorphism, also writing `phi_i` for the
induced bijection of character labels, and assume selector-equivariance

```text
S_i a=phi_i(a)S_i                    (a in A).          (PNF2)
```

Let `q_i` be any target carrier projection supported on the allowed target
characters,

```text
q_i<=p_(phi_i(R))^(i).                                  (PNF3)
```

Then the pulled-back nonscalar carriers

```text
r_i=S_i^*q_iS_i                                         (PNF4)
```

satisfy

```text
r_i<=Qp_R,       r_iF=0                 for every i.   (PNF5)
```

Consequently no finite number of such carriers can frame the common source:
for no `kappa>0` can one have

```text
sum_i r_i >= kappa Q.                                  (PNF6)
```

More sharply, every bridge pays the entire forbidden source mass,

```text
||(1-q_i)S_iF||_2^2=||F||_2^2.                         (PNF7)
```

Neither noncommutativity of the `q_i`, orthogonality of their target ranges,
nor arbitrary relative angles between their allowed parts changes this
common kernel.  Relabeling the predicate does not help: even when
`phi_i(R)` is a different subset in the target coordinates, its pullback is
the same source support `R`.

## Conjugate-frame specialization

Let a finite context packet `H` contain `A` and a selected central type
projection `q<=p_R`.  In any overgroup, take arbitrary elements `t_i` which
normalize `A` and whose induced permutations preserve `R`.  Then

```text
q_i=t_i q t_i^(-1)<=p_R,                               (PNF8)
```

so all the genuinely nonscalar conjugate projections `q_i` annihilate every
forbidden character atom.  This remains true if the `t_i` are free stable
letters and the allowed parts of the `q_i` are in maximally generic/free
position.  Free conjugation can improve angles only on `p_R`; it cannot move
mass across the invariant spectral wall `p_R`.

## Consequence for CPS9

The smallest proposed repair of the D8 compiler is to attach finitely many
conjugates of each selected context type to the one common partial-swap
source, hoping that their sum becomes a positive frame.  To keep every copy
as the **same** context predicate and to make its shared-variable rows
conjugate copies of one row, its transporter must normalize the context
selector algebra and preserve `R`.  Equations `(PNF5)--(PNF7)` then show
that the predicate's forbidden projection on the common source is precisely
the subspace missed by every copy.  Such a frame cannot imply `(CPS9)`.

This is a stronger obstruction than the scalar-bus failure: the transported
objects may be high-dimensional primitive packet blocks and the swaps may be
fully nonscalar.  The next architecture must use at least one transporter
which does **not** preserve the selector support.  It must mix selectors with
payload while still returning all copies to one literal shared-variable row.
Merely replacing scalar buses by type projections, free conjugates, or
orthogonal partial-swap ranges does not cross the global carrier-alignment
seam.
