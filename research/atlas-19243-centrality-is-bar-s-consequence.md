---
rg: 2
id: atlas-19243-centrality-is-bar-s-consequence
kind: claim
title: The word-19243 interior centrality test is forced by the canonical atlas packet
artifacts:
  - docs/EXPLICIT_LEAVITT_ATLAS.md
  - docs/ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT.md
  - experiments/atlas-word-19243.json
---

Let

```text
bar_rho : bar_P=K_1*K_2 -> Q
N       = ker(bar_rho),
bar_N   = [bar_P,N].
```

Let `q_19243` be the eight-syllable interior collision word and let `x` be the
fixed first-chart transvection `p1_12` used in the exact rank-three audit.  Put

```text
c_19243 = [x,q_19243].
```

Then

```text
c_19243 in bar_N = <<bar_S>>,
```

where `bar_S` is the canonical finite normal generating packet from
`leavitt-regular-atlas-hyperlinearity-criterion`.

Consequently there is a fixed integer `L_19243` such that every unitary
representation `pi` of `bar_P` satisfies

```text
||pi(c_19243)-1||_2
 <= L_19243 * max_(s in bar_S) ||pi(s)-1||_2.
```

In particular, along every canonical regular-atlas microstate sequence, the
interior centrality defect tends to zero automatically.  Thus the interior
separator singled out by the exact boundary audit does **not** require a new
normal-closure computation: it is already a formal consequence of the packet
by which the atlas criterion is defined.