---
rg: 2
id: smallest-target-sign-split-is-regularly-absorbed
kind: claim
title: The smallest noncentral target-sign split gives one escape and is then regularly absorbed
distinct_from:
  two-reynolds-edges-absorb-selector-holonomy-at-one-range: that gives two phase-distinct paths with exactly one common range; this proves a fixed target observable cannot distinguish such paths and then constructs the minimal genuinely split target.
  index-two-reynolds-atoms-have-orthogonal-hnn-transports: that gives arbitrary elementary-abelian orthogonal character destinations; this identifies the smallest packet and computes its exact HS mismatch and saturation hull.
  two-orientation-hnn-packet-prepays-escape: that uses rank-one/rank-three controlled-Pauli orientations; this gives the four-character elementary-abelian model with no Clifford representation theory.
---

**ESTABLISHED MINIMAL LOCAL ESCAPE AND REGULAR FIREWALL.**  First, a single
fixed target observable cannot split two same-range paths.  If `D_0,D_1` are
projections and `Y` is a contraction, then

```text
||D_0YD_0-D_1YD_1||_2<=2||D_0-D_1||_2.                (NTS1)
```

Indeed insert `D_1YD_0` and use operator-norm contractivity.  In particular,
if `D_0=D_1`, the two compressions are identical.  Thus adding a target
involution to the same-range model of
`two-reynolds-edges-absorb-selector-holonomy-at-one-range` cannot create
escape; any fixed compression gap already presupposes a support gap of at
least half its size.

The smallest genuine support split uses

```text
T=C_2^2,             K=GL_2(F_2)~=S_3.                (NTS2)
```

For the three nontrivial characters `chi_s,chi_0,chi_1` of `T`, let

```text
D_i=e_(ker chi_i)-e_T.                                 (NTS3)
```

These are the three nontrivial minimal character projections in `C[T]`:

```text
D_iD_j=0  (i!=j),       tau_reg(D_i)=1/4.              (NTS4)
```

Choose `k_0,k_1 in K` with `k_i chi_s=chi_i`.  The finite affine packet
`T rtimes K` gives ordinary covariance words satisfying

```text
k_iD_sk_i^*=D_i.                                       (NTS5)
```

There is a target involution `y in T` with
`chi_0(y)=-chi_1(y)`, and hence

```text
D_0yD_0=-D_0,             D_1yD_1=D_1                (NTS6)
```

after exchanging labels if necessary.

Tensor with any payload projection `F` commuting with this packet.  Put

```text
A=FD_s,            A_i=k_iAk_i^*=FD_i.                (NTS7)
```

Then the consequence is payload-vacuous at `F=0`, while for positive `F`
it gives complete one-step escape and the exact HS target mismatch

```text
A_0A_1=0,
||A_0-A_1||_2^2=tau(A_0)+tau(A_1)=tau(F)/2.            (NTS8)
```

All constants are dimension independent and fixed packet correction changes
them by only `O(sqrt(E_pres))`.

This local success is exactly regularly absorbed.  In the left regular
representation of `T rtimes K`, all three `D_i` occur with equal density and
the reducing hull of any one under the two actor words is

```text
D_s+D_0+D_1=1-e_T,             tau=3/4.                (NTS9)
```

Every packet and covariance relator has zero defect.  Tensoring with the
uniform positive-forbidden BCS model keeps `F` positive, so `(NTS8)` is a
real local escape but the orbit saturates after one finite packet.  Reusing
the packet gives no further growth.  Using `N` fresh packets requires a
specified source character in every future factor, prepaying density
`4^(-N)`; opening the factors can recover only that prepaid capacity.

Therefore the smallest noncentral target observable does not yield a finite-
depth contradiction.  It sharpens the surviving seam: the target support
must carry a nonstationary label whose positive payload mass is not already
distributed over a finite regular orbit.  Any finite character packet,
including this minimal one, is capacity preserving.

DERIVATION
four-character-target-sign-regular-absorption-proof
