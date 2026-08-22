---
rg: 2
id: atlas-q96-c144-cycle-is-perfect-with-overlap-curvature
kind: claim
title: The six-generator Q96-C144 cycle is perfect and evades the naive square-curvature theorem
distinct_from:
  atlas-q96-to-c144-cycle-is-six-generator-finite-vertex-test: that freezes the presentation and its marked finite vertices; this Tietze-reduces it, computes all solvable quotients, and audits the tempting polygon-of-groups argument.
---

The universal six-generator cycle has trivial abelianization.  Hence every
homomorphism from it to a solvable group is trivial; any faithful finite-vertex
quotient must be nonsolvable and have order divisible by 288.

Replacing `s` by `b=st` gives a shorter marked presentation in which the two
forward-fan relations are simply `(r^-1 b)^3=(zb)^3=1` and the collision word
is `t c b t^-1 c t^-1 c b c`.

The balanced four-vertex diagram is not directly covered by the standard
nonpositive-curvature polygon theorem.  At the `Q96` corner, the two incident
marked subgroups `V4=<c,u>` and `A4=<c,t>` intersect in `<c>`, although the
other two square edges do not contain that subgroup.  Treating the face group
as trivial creates a length-two kernel word at this corner (angle `pi`), while
using `<c>` as face group is incompatible with the other edges.  Thus an
explicit completion or a more refined complex-of-groups subdivision is
needed; the marginal angle sum alone cannot prove developability.

