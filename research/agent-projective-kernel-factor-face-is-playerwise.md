---
rg: 2
id: agent-projective-kernel-factor-face-is-playerwise
kind: claim
title: A factorial left-right projective-kernel CE face is exactly playerwise
artifacts:
  - research/agent-projective-kernel-factor-face-is-playerwise-proof.md
distinct_from:
  factor-split-projective-kernel-face-meets-fd-closure: that constructs a product vector state in the finite-dimensional-state closure for every scalar subface; this computes the full projective kernel and gives an exact equivalence for Connes-embeddable tracial faces.
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that shows a raw one-player projective kernel need not have a CE gap; this proves that the two-player factorial linking representation cannot create such a gap unless one player already has it.
---

Let `G_A,G_B` act in the standard left-right representation of a factor
`(M,tau)`:

```text
pi(a,b)=L(u_a) R(v_b) on L^2(M,tau).                  (APF1)
```

Write `K_pi` for the projective kernel of `pi` and `chi_pi` for its scalar
character.  Define the projective kernels of the two commuting player
representations by

```text
K_A={a:L(u_a) is scalar},       L(u_a)=alpha(a)I,
K_B={b:R(v_b) is scalar},       R(v_b)=beta(b)I.       (APF2)
```

Then

```text
K_pi=K_A x K_B,
chi_pi(a,b)=alpha(a) beta(b).                          (APF3)
```

Moreover, with `T_CE(G)` denoting the Connes-embeddable tracial states and
`F_(K,chi)^tr` the tracial scalar-character face,

```text
F_(K_pi,chi_pi)^tr intersect T_CE(G_A x G_B) != empty

iff

F_(K_A,alpha)^tr intersect T_CE(G_A) != empty
and
F_(K_B,beta)^tr intersect T_CE(G_B) != empty.         (APF4)
```

Consequently, if `K<=K_pi` and `chi=chi_pi|K`, then

```text
F_(K,chi)^tr intersect T_CE(G_A x G_B)=empty          (APF5)
```

implies that at least one of the two one-player full projective-kernel faces
in `(APF4)` contains no CE trace.

Thus the factorial two-player monomial linking structure cannot manufacture
a projective-kernel CE gap.  Any such gap already occurs on one player.  This
does not assert that either one-player face is empty merely because the
original trace is non-CE; that invalid promotion is still excluded by
`non-ce-trace-does-not-promote-to-subgroup-character-gap`.

