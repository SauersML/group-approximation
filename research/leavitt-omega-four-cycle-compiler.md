---
rg: 2
id: leavitt-omega-four-cycle-compiler
kind: claim
title: A two-corner four-cycle compiles the Leavitt Omega mismatch
artifacts:
  - research/leavitt-omega-four-cycle-compiler-proof.md
distinct_from:
  leavitt-two-relator-corner-peeling: that identifies the minimal nonpeelable incidence and gives an abstract h-labeled sharpness example; this instantiates its two labels with the explicit source and target Omega values in the Leavitt group.
  kl-test-word-conjunction-fence: that excludes a singular coefficient-free conjunction; this is a post-pivot system with a nonzero-degree pivot and a repeated long-corner two-core.
---

Let `H,Y` be formal long-corner generators and let

```text
D=<the Leavitt coefficient gates>,
S=Omega(a,r)=1,              T=Omega(c,p)=h!=1.
```

Then the post-pivot corner presentation

```text
P=<D,H,Y | Y S H^(-1), Y T H^(-1)>
```

kills `h`.  Its long-corner incidence is the minimal four-cycle: both `H`
and `Y` occur in both relators, so neither relator nor long generator admits
the singleton peeling move.

Thus realizing these two relators together with one unary pivot orbit in a
nonzero-degree cyclic cover would give a KL coefficient collapse.  The
remaining problem is purely cyclic realization of the repeated corners.
