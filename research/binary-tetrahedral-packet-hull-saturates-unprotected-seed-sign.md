---
rg: 2
id: binary-tetrahedral-packet-hull-saturates-unprotected-seed-sign
kind: claim
title: A binary-tetrahedral packet hull saturates every unprotected seed half
distinct_from:
  agent-aggregate-escape-atomwise-seed-flip-saturates: That saturates the marked sector after transporting the whole forbidden aggregate with the Pauli mate; this saturation occurs already at initialization, from one quaternion element in the root-detection packet.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: That solves finite restriction multiplicities abstractly; this computes the exact canonical reducing hull in the binary-tetrahedral Bass--Serre amalgam.
  binary-tetrahedral-conditional-e5-root-bridge: That proves the local root-compression inequality on a packet-reducing carrier; this shows that making the original seed carrier packet-reducing consumes the proposed capacity unless the seed sign is included in the amalgamated subgroup.
---

**ESTABLISHED CAPACITY FIREWALL.**  In the amalgam `(BTB2)`, let `B_0` be
an involution in the base factor which does not belong to the amalgamated
subgroup

```text
A=H times <Z> times <ell>.
```

Assume `B_0` commutes with the central involutions `J,ell`, as does the
Pauli seed sign in the canonical BTB construction.  Choose a quaternion
element

```text
t in T \ <Z,ell>.
```

Bass--Serre normal form gives

```text
<B_0,tB_0t^(-1)> isomorphic to C_2*C_2.               (BHS1)
```

Indeed, every nonempty alternating word in the two displayed involutions
expands to a reduced amalgam word.  In particular

```text
r=B_0tB_0t^(-1)
```

has infinite order.

Let

```text
c=q_J^- q_ell^-,       e=c(1+B_0)/2.                  (BHS2)
```

In the canonical left regular representation, the two projections

```text
e,       tet^(-1)=c(1+tB_0t^(-1))/2
```

have join exactly `c`.  To see this, a vector in the complementary meet
would be a `-1` eigenvector of both free involutions, hence a fixed vector
of `r`.  Left translation by an infinite-order group element has no nonzero
fixed vector in `ell^2(Gamma)`.  Therefore

```text
e join tet^(-1)=c.                                    (BHS3)
```

Consequently every projection `Q` which contains `e`, reduces the attached
binary-tetrahedral packet, and lies below `c`, satisfies

```text
Q=c.                                                   (BHS4)
```

The same conclusion holds asymptotically in canonical normalized-HS
microstates.  After rounding the two involutions, the complementary meet is
contained in the fixed space of the rounded word `r`.  For every `N`, the
fixed-space projection is bounded in trace by the squared Hilbert--Schmidt
norm of

```text
N^(-1) sum_(k=0)^(N-1) rho(r)^k.
```

All nonzero powers of `r` have canonical group trace zero by `(BHS1)`.
First letting the microstate defect tend to zero and then `N` tend to
infinity makes the complementary meet `o(1)`.  Hence the packet-reducing
hull of `e` has trace

```text
tr(Q)=tr(c)+o(1)=1/4+o(1).                            (BHS5)
```

This applies to the current formulation of
`canonical-bcs-root-detection-via-binary-tetrahedral-bridge`: its seed sign
is independent of every edge group, while `Q_empty` is required to reduce
all attached packets.  The proposed seed hull therefore already fills the
whole `J=-1,ell=-1` capacity.  No positive-growth recurrence can start from
that hull.

There is one exact local repair.  If a finite sign packet `K` commutes with
the source root, replace the edge and packet factors by

```text
H times K times <Z> times <ell>
    -> H times K times T,                             (BHS6)
```

so the entire binary-tetrahedral packet centralizes `K`.  Then the argument
above does not move a `K`-character seed.  Every literal seed or prefix sign
whose half-space is to survive packet reduction must be protected this way;
omitting even one such sign recreates `(BHS1)--(BHS5)`.

For the adaptive tree, `(BHS6)` is now implemented by
`protected-adaptive-btb-wordization-preserves-canonical-budget`.  It adds
`[q_sigma,B_0]=[d_(sigma,i),B_0]=0`, includes `J` as well as `B_0` in the
edge two-group, and proves the characteristic-three wordization and edge
injections.  Protecting the seed removes the initialization collapse; it
still does not prove `(CBR3)`.

DERIVATION
binary-tetrahedral-packet-hull-saturates-unprotected-seed-sign via binary-tetrahedral-free-conjugate-hull-proof
