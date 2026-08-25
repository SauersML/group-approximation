---
rg: 2
id: a4-role-atom-has-flat-c3-root-overlap
kind: claim
title: An A4 role atom has flat C3-root overlap on every reducing multiplicity carrier
distinct_from:
  coprime-root-reynolds-prefix-overlap: That computes canonical trace for a fixed two-primary Reynolds projection; this is a representation-level compression identity valid after an arbitrary analytic cut in the A4 commutant.
  bcs-atom-detects-its-e5-central-root: That must detect the coefficient-dependent E5 root which collapses when the payload idempotent vanishes; this detects an auxiliary A4 root which remains nontrivial independently of the payload.
  e5-idempotent-root-has-two-pair-extraspecial-cell: That splits a source after its E5 center is known to be nontrivial; this gives a one-pair finite-group model showing that nonliteral reducing hulls themselves cause no overlap loss.
---

**ESTABLISHED MIXED-ROW LEMMA.**  Write

```text
K=A4=V4 semidirect <z>,             |z|=3,
```

where conjugation by `z` cycles the three nontrivial characters of `V4`.
Let `c_3` be the central projection of `C[K]` for the three-dimensional
irreducible representation and let `r_chi` be the Fourier projection of one
nontrivial character `chi` of `V4`.  Put

```text
p_z=(1+z+z^2)/3,             s_z=1-p_z.               (AMR1)
```

In every unitary representation of `K`, for every projection `Q` commuting
with `K` and satisfying `Q<=c_3`, and every projection `P` commuting with
`K` and `Q`, the possibly nonliteral projection

```text
E=Q P r_chi                                             (AMR2)
```

satisfies the exact identities

```text
E p_z E=(1/3)E,
tr(E s_z)=(2/3)tr(E).                                  (AMR3)
```

Thus the estimate survives an arbitrary analytic reducing hull or decoded
multiplicity corner.  It is not a canonical-word-moment calculation.

Tensoring `k` copies gives `3^k` pairwise orthogonal role atoms in the
selected block `c_3^(tensor k)`.  For any chosen atom and any coordinate,
the corresponding `C3` root has the same flat one-third compression.  This
can replace an extraspecial role menu without losing the fixed inverse-menu
factor: if the BCS generators commute with the packet and `Q` lies in the
selected block, every role atom has trace `3^(-k)tr(Q)` and `(AMR3)` remains
valid after multiplication by the associated forbidden BCS projection.

The lemma does **not** identify this auxiliary order-three word with the
coefficient root `x_13(a)` of the adaptive Steinberg compiler.  In the
perfect coefficient model the forbidden idempotent `a` is zero, hence
`x_13(a)=1`, while `z` is nontrivial on the selected `A4` block.  Literal
amalgamation therefore destroys that model.  A conditional bridge would
have to make the A4 block itself vanish with `a`, and reflecting that
conditional block from an abstract Steinberg microstate is exactly the
payload-to-root problem again.

DERIVATION
a4-role-atom-flat-c3-compression-proof
