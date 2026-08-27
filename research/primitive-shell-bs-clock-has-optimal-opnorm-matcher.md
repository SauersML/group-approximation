---
rg: 2
id: primitive-shell-bs-clock-has-optimal-opnorm-matcher
kind: claim
title: The primitive 3-power BS shell has an asymptotically optimal operator-norm matcher
artifacts:
  - research/primitive-shell-bs-clock-has-optimal-opnorm-matcher-proof.md
distinct_from:
  periodic-higman-bs-clocks-have-three-opnorm-small-seams: that uses the whole q-dimensional periodic clock and obtains an O(n/3^n) ordered-spectrum matcher; this restricts to the single primitive shell, makes the joint commutant scalar, and obtains the optimal Theta(3^(-n)) scale.
  order-four-bs-matcher-builds-higman-opnorm-microstate: that shows a matcher with a vanishing fourth return gives a Higman microstate; this supplies a sharper one-step matcher but does not control its fourth return.
---

**ESTABLISHED.**  Put `q=3^n`, `L=phi(q)=2*3^(n-1)`, and let

```text
H_n=span{e_x : x in (Z/qZ)^*}.
```

The periodic clock restricts to an exact packet on `H_n`:

```text
D e_x=exp(2 pi i x/q)e_x,
P e_x=e_(2^(-1)x),
P D P^*=D^2.                                         (PSM1)
```

There is a unitary matcher `K_n on H_n` satisfying

```text
2 sin(pi/q)
 <= ||D-K_n P K_n^*||_op
 <= 2 pi/q.                                          (PSM2)
```

The lower bound applies to every unitary matcher, so this scale is
asymptotically optimal.  Moreover

```text
||P-1||_op=2,
{P,D}'=C 1.                                          (PSM3)
```

Thus nested lower-order shells and their multiplicities are not needed for
the remaining Higman matcher test.  A sequence of matchers on these
primitive shells with

```text
||K_n^4 P K_n^(-4)-P||_op ->0                        (PSM4)
```

would already give the noncollapsing Higman operator-norm microstate of
`order-four-bs-matcher-builds-higman-opnorm-microstate`.  Conversely this
claim proves no estimate on `(PSM4)`: the fourth return remains the sole
unpaid gate.
