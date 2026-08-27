---
rg: 2
id: canonical-btb-static-packing-has-capacity-ceiling
kind: claim
title: Static packing of binary-tetrahedral detected mass has the exact canonical capacity ceiling
root: true
artifacts:
  - research/canonical-btb-static-packing-capacity-proof.md
distinct_from:
  canonical-trace-forbids-supercritical-character-packing: That treats the original bad-character projection in the marked half; this treats its order-three detected subprojection and separates literal group-algebra packing from the analytic reducing-hull carrier.
  canonical-btb-finite-depth-escape-tree: That asks for one payload-conditioned outside-carrier return and then enlarges the carrier; this rules out replacing that return by finitely many static packet refinements and HNN conjugates.
  finite-tags-do-not-atomize-heisenberg-schrodinger-tower: That computes exponential fine-character decay in a nested Heisenberg tower; this gives the direct canonical capacity certificate for every finite literal BTB/Heisenberg refinement.
---

Let `G` contain the finite seed/context groups and the canonical
binary-tetrahedral extension of
`canonical-bcs-root-detection-via-binary-tetrahedral-bridge`.  Put

```text
C=q_J^-q_ell^-,                 tau_G(C)=1/4.           (BSP1)
```

There are two different objects which must not be conflated.

### Literal static detector

Let `L<=C` be any fixed finite-two-group character projection reducing the
shared contextual tuple, let

```text
e_i=LP_i,
d_i=e_i S_(Z_i),                                       (BSP2)
```

and assume `Z_i` is the exact order-three source root commuting with `e_i`.
These are fixed projections in the group algebra.  Coprimality gives in the
canonical group trace

```text
tau_G(d_i)=(2/3)tau_G(e_i).                            (BSP3)
```

If `tau_G(L)=a` and exact uniform contextual soundness gives

```text
sum_i tau_G(e_i)>=beta a,                              (BSP4)
```

then `K` pairwise orthogonal conjugates of every `d_i`, all below `C`, obey

```text
K<=3M tau_G(C)/(2 beta a)                              (BSP5)
```

when orthogonality is only within each fixed type, and

```text
K<=3 tau_G(C)/(2 beta a)                               (BSP6)
```

when all types are packed simultaneously.  For the literal BTB Pauli seed
`a=1/8`, these become

```text
K<=3M/beta,                    K<=3/beta.               (BSP7)
```

They are stricter than the `4M/beta` and `4/beta` thresholds obtainable
from the representation-uniform one-half BTB estimate on an analytic
carrier.  Therefore the required static packing identities cannot hold
while the finite seed, context, and order-three root subgroups remain
embedded.

### Analytic detected carrier

For the actual BTB adaptive route one instead has

```text
E_i=QP_i,                 D_i=E_iS_(Z_i),              (BSP8)
```

where `Q` is the representation-dependent common reducing hull.  The bridge
does prove

```text
tau(D_i)>=(1/2)tau(E_i)-o(1)                           (BSP9)
```

in canonical matrix microstates.  But `Q`, and hence `D_i`, is not a fixed
element of the ordinary group algebra.  A finite HNN relation can conjugate
`d_i` from `(BSP2)`; it cannot directly name the spectral support projection
defining `Q` in each representation.  Any theorem that makes word transport
depend on `(BSP8)` is precisely a payload-conditioned analytic
carrier-return theorem of the kind required in `(CBR3)`, not a static
packing construction.

Finitely many further binary-tetrahedral or Heisenberg packets do not change
this dichotomy.  Orthogonal finite packet atoms partition the old source
trace; overlapping detectors cannot be summed; and once fixed group-word
translates are made orthogonal under `C`, canonical trace gives
`(BSP5)--(BSP6)`.  Packet/HNN covariance alone also retains the regular
stationary multiplicity profile.

The perfect marked representation may send `ell` and every auxiliary packet
to one.  That preserves perfect completeness but does not change the
canonical trace of the abstract group.  Hence nonfaithfulness of the perfect
model does not evade the literal ceiling.  The live route remains a selected
piece escaping its **current analytic carrier**, followed by carrier
enlargement; no finite static packing of named packet projections replaces
that step.

DERIVATION
canonical-btb-static-packing-capacity-proof
