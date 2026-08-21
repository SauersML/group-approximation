---
rg: 2
id: expander-edge-overlay-detects-simplex-exterior-square
kind: claim
title: A constant-degree edge overlay robustly detects every simplex-code wedge
distinct_from:
  local-exterior-square-kernel-yields-pauli-strategy: that gives the necessary obstruction for an arbitrary local code presentation; this constructs a bounded-degree overlay that removes the obstruction on affine/simplex global sections.
  two-copy-overlap-consistency-has-pauli-cycle-countermodel: that uses a code with macroscopically supported locally proportional cycle sections; simplex sections have balanced affine fibers, which the expander overlay samples.
---

ESTABLISHED.  Put `A=F_2^n` and let

```text
C_n = {x |-> a.x+c : a in F_2^n, c in F_2}                 (SEO1)
```

be the affine binary simplex code.  There is a universal degree bound `d` and,
for every `n`, a regular graph `G_n` of degree at most `d` on `A` such that the
following holds.
For `u,v in C_n`, set `p_x=(u(x),v(x)) in F_2^2` and

```text
D(u,v) = Pr_(x,y in A)[det(p_x,p_y)=1],
L_G(u,v) = Pr_(directed edge x~y)[det(p_x,p_y)=1].          (SEO2)
```

Then one may choose the graphs so that

```text
D(u,v) <= (8/5) L_G(u,v).                                  (SEO3)
```

In particular, the restriction map on decomposable exterior squares is
uniformly robust: if `u,v` are independent, at least `15/64` of the directed
edge views have rank two.  If they are dependent, both sides of `(SEO3)`
vanish.

Consequently any bounded-degree classical LTC/PCPP presentation of `C_n` can
be given the required first-layer noncontextuality check by overlaying the
edges of `G_n` as unrestricted two-coordinate local views and asking for one
joint PVM on each edge.  The overlay has one fixed answer template, raises
coordinate incidence by only `d`, introduces no equality fibers, and two
distinct edge views share at most one coordinate.  Exact classical global
sections remain exactly `C_n` because the new views impose no classical
constraint.

This closes the Pauli/exterior-square obstruction only after the local views
have been decoded to global simplex sections.  It does not by itself turn an
arbitrary family of edgewise commuting operator views into one global PVM;
that higher contextual agreement step remains the operator-valued content of
`bounded-template-average-blr-occurrence-decoder`.
