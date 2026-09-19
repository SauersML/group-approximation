---
rg: 2
id: binary-tetrahedral-conditional-e5-root-bridge
kind: claim
title: A binary-tetrahedral amalgam detects an exact order-three coefficient root on every negative central-sign reducing carrier
distinct_from:
  a4-role-atom-has-flat-c3-root-overlap: That uses the selected three-dimensional A4 block; this has one common central involution and a uniform bound on every irreducible type in its negative sector.
  bcs-atom-detects-its-e5-central-root: That is the payload estimate inside the full finite adaptive compiler; this is the exact one-source Bass--Serre bridge and its representation-level inequality.
  agent-packet-root-finite-detectors-are-normal-quotient-selectors: That classifies detectors using a packet projection already in the old finite subgroup; this introduces a fresh central sector, uses it only in canonical microstates, and permits that sector to vanish in the perfect representation.
---

**ESTABLISHED CONDITIONAL ROOT BRIDGE.**  Let `B` contain a finite
two-group `H` and an element `Z` such that

```text
|Z|=3,                 [Z,H]=1.                        (BTB1)
```

Adjoin one independent central involution `ell`.  Let

```text
T=Q8 semidirect <y> congruent SL_2(F_3),
|y|=3,
```

where `y` cyclically permutes the three order-four axes of `Q8`, and identify
the central involution of `Q8` with `ell`.  The subgroup `<y,ell>` is
`C3 times C2`.  Form the ordinary amalgam

```text
G=(B times <ell>)
     *_(H times <Z> times <ell>)
   (H times T),                                         (BTB2)
```

where `y` is identified with `Z`.  Both maps in `(BTB2)` are injective, so
Bass--Serre normal form embeds `B times <ell>` and `H times T` in `G`.

Let `e_chi` be any character projection of `H`.  In every finite-dimensional
unitary representation of `G`, if `Q` is a projection reducing `H times T`
and

```text
Q <= q_ell^-=(1-ell)/2,
E=Q e_chi,                                             (BTB3)
```

then, for the nontrivial spectral projection

```text
S_Z=1-(1+Z+Z^2)/3,
```

one has the dimension-free estimate

```text
tr(E S_Z) >= (1/2) tr(E).                              (BTB4)
```

This is valid for an arbitrary analytic reducing hull `Q`; no canonical
moment formula for `Q` is used.  Fixed finite-group correction gives the
normalized-HS version with an `O(sqrt(E_pres))` loss.

The bridge preserves the intended perfect representation.  If a
representation of `B` sends `Z` to one, extend it by sending `ell` and the
whole factor `T` to one and retaining the given action of `H`.  The two
restrictions to the amalgamated subgroup agree.  Thus a forbidden
coefficient `a=0`, and hence `x_13(a)=1`, is fully compatible with `(BTB2)`;
the negative `ell` carrier is simply absent in that representation.

For a fixed finite adaptive menu, use characteristic three and attach one
copy `T_(sigma,i)` for each named source root, all sharing the same fresh
central involution `ell`.  Iterated amalgamation preserves the original
wordized group and every previously attached finite factor.  In a canonical
microstate the embedded involution `ell` has asymptotically equal positive
and negative sectors.  Start from the Pauli seed cut by `q_ell^-`, and at
each stage take the common reducing hull for the shared BCS tuple and the
finitely many attached packets.  Since `J` and `ell` are central, every such
hull and every marked transport remains below their common negative sector.
Each individual source is then in the situation `(BTB3)--(BTB4)`.

The last paragraph is a **canonical-microstate** device, not a statement
about arbitrary approximate representations which merely keep the old mark
`J` separated.  Such a representation may send the independent `ell` to
one.  This distinction is harmless for a direct nonhyperlinearity proof,
because hyperlinearity supplies microstates for the canonical group trace,
but it must not be silently substituted into a stronger marked-word
stability statement.

DERIVATION
binary-tetrahedral-spin-root-compression-proof
