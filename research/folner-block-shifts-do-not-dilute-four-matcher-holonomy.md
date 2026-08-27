---
rg: 2
id: folner-block-shifts-do-not-dilute-four-matcher-holonomy
kind: claim
title: Folner block shifts dilute one BS matcher seam but replicate the fourth-power holonomy in bulk
artifacts:
  - research/artifacts/higman-bs-packet-product-holonomy-2026-08-21.md
distinct_from:
  three-higman-bs-seams-vanish-fourth-is-product-holonomy: that isolates the homogeneous order-four matcher term; this tests the proposed long-path block-shift amplification and proves that term remains on almost every interior block.
  long-cycles-have-unbounded-l2-coboundary-inverse: that concerns inversion of a scalar cyclic coboundary; this is an exact matrix block computation for the four-step Higman return.
  split-higman-cycle-has-haar-marginals-and-maximal-role-gap: that keeps each one-step occurrence seam large; here the one-step matcher error and its cyclic wrap both dilute, but the four-step return does not.
---

Let `(P,D)` be any exact finite-dimensional `BS(1,2)` packet and let `S` be
an `epsilon` spectral matcher:

```text
PDP^(-1)=D^2,             ||D-SPS^*||_2=epsilon.      (FBS1)
```

On `L` equal blocks define

```text
P^(L)=direct_sum_(k=0)^(L-1) S^k P S^(-k),
D^(L)=direct_sum_(k=0)^(L-1) S^k D S^(-k).           (FBS2)
```

This is again an exact BS packet.  Let `T_L` be the cyclic block shift in
the orientation for which conjugating `P^(L)` advances `k` to `k+1`.  Then

```text
||D^(L)-T_L P^(L) T_L^*||_2^2
    <= epsilon^2+4/L.                                 (FBS3)
```

Thus the long block cycle really does dilute the single wrap of the one-step
matcher.

However, put

```text
h=||S^4 P S^(-4)-P||_2.
```

On each of the `L-4` nonwrapping blocks, the fourth-power return compares
`S^(k+4)PS^(-(k+4))` with `S^kPS^(-k)` and therefore has norm exactly `h`.
Only four blocks meet the cyclic boundary.  Consequently

```text
(1-4/L)h^2
 <= ||T_L^4 P^(L) T_L^(-4)-P^(L)||_2^2
 <= (1-4/L)h^2+16/L.                                 (FBS4)
```

In particular the fourth-power holonomy converges to `h`; it is replicated
through the Folner bulk rather than confined to the wrap.

This rules out the proposed long-path dilution in the homogeneous periodic-
packet sector.  Pairing the eigenvalues of `P` and `D` in quartets does not
establish `T_L^4=I` or `(FBS4)=o(1)`: an optimal normal-matrix matcher maps
the eigenbasis of `P` to the generally different eigenbasis of `D`, and its
fourth power depends on the product of those basis transports, not on the
four matched eigenvalues alone.  An order-four matcher would already satisfy
the unresolved joint eigenbasis holonomy condition.

More generally, a varying long path of packet gauges replaces `S^4` in each
interior block by the ordered product of the four consecutive matcher
increments.  Fixed four-generator folding therefore tests a four-step return
at positive density.  It cannot move all incompatibility to one terminal
block unless those local four-step products already asymptotically centralize
their packet conjugators.

