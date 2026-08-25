---
rg: 2
id: binary-leavitt-two-branch-character-restriction-proof
kind: route
title: Split every coefficient into its two right-prefix components and dualize
target: binary-leavitt-two-branch-character-restriction-is-faithful
requires: []
---

The Leavitt completeness relation gives, for every `r in R`,

```text
r=(r s_0)t_0+(r s_1)t_1.                              (BCR4)
```

The sum is direct: if `a_0t_0+a_1t_1=0`, multiplication on the right by
`s_j` gives `a_j=0`.  Hence the additive map

```text
R -> R directSum R,                  r |-> (r s_0,r s_1)
```

has inverse `(a_0,a_1) |-> a_0t_0+a_1t_1`.

Dualizing this explicit additive-group isomorphism gives `(BCR2)`.  Directly,
the character in `(BCR3)` satisfies

```text
F_j(chi)(a)
 =phi_0(a t_j s_0) phi_1(a t_j s_1)
 =phi_j(a),
```

while `(BCR4)` gives

```text
chi(r)=F_0(chi)(r s_0) F_1(chi)(r s_1).
```

Thus the displayed maps are mutual inverses.  This is a character-label
identity only: it supplies no commutation, overlap, or common-carrier theorem
for projections transported by two different ambient branch conjugators.
