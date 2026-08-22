---
rg: 2
id: atlas-q96-c144-cycle-is-perfect-with-overlap-curvature-proof
kind: route
title: Tietze-rewrite, abelianize, and inspect the Q96 corner intersection
target: atlas-q96-c144-cycle-is-perfect-with-overlap-curvature
requires:
  - atlas-q96-to-c144-cycle-is-six-generator-finite-vertex-test
  - atlas-forward-fan-cycle-is-balanced-s288-square
---

Put `b=st`, so `s=b t^-1`.  The `S3` relations on `s,t` become

```text
b^2=1,       b t b=t^-1.                              (PC-1)
```

Direct substitution in collision gives

```text
q=t c b t^-1 c t^-1 c b c.                           (PC-2)
```

The remaining fan relations are `(r^-1b)^3=(zb)^3=1`; all other relators are
the displayed finite-vertex relators from the six-generator presentation.
Equations `(PC-1)`--`(PC-2)` are Tietze-equivalent to the original use of `s`.

For the abelianization, use additive notation.  From `r^3=1` and `(ur)^2=1`
with `u^2=1`, obtain `3r=2r=0`, hence `r=0`.  Similarly `z^3=1` and
`(cz)^2=1` give `z=0`.  From `t^3=1` and `(st)^2=1` obtain `t=0`.
Then `(ct)^3=1` gives `c=0`, and `(ut)^3=1` gives `u=0`.  Finally
`(r^-1st)^3=1` gives `s=0`.  Thus every generator vanishes and

```text
G_ab=1.                                               (PC-3)
```

Every quotient of a perfect group is perfect.  A perfect solvable group is
trivial, proving the solvable-quotient assertion.  A quotient preserving all
four marked vertices has order divisible by

```text
lcm(36,96,24,144)=288.                                (PC-4)
```

For the curvature audit, the two square edges incident at `Q96` have groups
`V4=<c,u>` and `A4=<c,t>`.  Their images intersect in `<c>` of order two.  If
the square face group is trivial, the two copies of `c` give an alternating
kernel word of length two, so the Gersten--Stallings angle at that corner is
`pi`, not the `pi/3` suggested by only looking at `(ut)^3`.  The face group
cannot instead be `<c>`, since `<c>` does not embed in the opposite `A=C3^2`
and `B=C2` edges with the required labels.  This proves the stated firewall
against the naive square-curvature argument.
