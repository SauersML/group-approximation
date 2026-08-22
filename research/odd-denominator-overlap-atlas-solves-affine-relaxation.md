---
rg: 2
id: odd-denominator-overlap-atlas-solves-affine-relaxation
kind: claim
title: An odd-denominator overlap atlas gives a classical point of the affine-support LCS
distinct_from:
  tracial-bcs-rationalizes-full-overlap-distributions: that supplies rational compatible context weights without controlling the parity of a common denominator; this identifies exactly what an odd denominator would imply after reduction modulo two.
  linear-encoding-lcs-admits-odd-subset-cheats: that classifies the odd-subset characters retained by a general exact linear encoding; this constructs one such character canonically from a rational overlap atlas.
  bcs-to-lcs-exact-support-gap: that asks whether an affine-support relaxation can retain the non-RU gap; this gives a necessary arithmetic condition on any witness to that possibility.
---

Let `B` be a finite BCS and choose nonempty context supports
`S_c subseteq R_c`.  Suppose there are nonnegative integers

```text
m_(c,a),       a in S_c,
```

and one **odd** integer `D` such that

```text
sum_(a in S_c) m_(c,a)=D                              (ODA1)
```

for every context, and such that the induced multiplicities of every full
overlap pattern agree: for contexts `c,d`, `I=V_c intersect V_d`, and
`sigma in F_2^I`,

```text
sum_(a in S_c:a|_I=sigma) m_(c,a)
 = sum_(b in S_d:b|_I=sigma) m_(d,b).                 (ODA2)
```

Then the affine-support relaxation with local relations
`Aff_F2(S_c)` has a classical solution.  Explicitly, reduce the multiplicities
modulo two and put

```text
T_c={a in S_c:m_(c,a) is odd},
x_c=sum_(a in T_c) a in F_2^(V_c).                    (ODA3)
```

Every `T_c` is odd, so `x_c in Aff_F2(S_c)`, and `(ODA2)` makes the points
`x_c` agree on all context overlaps.  They therefore glue to one global
boolean assignment satisfying every affine-support row.

Consequently, if `tau` is a satisfying trace and `L_tau` is its
affine-support relaxation, then

```text
L_tau not R^U-satisfiable
  ==> every rational full-overlap atlas supported on S_c(tau)
      has even common denominator.                    (ODA4)
```

Here a rational atlas `mu_(c,a)` is converted to `(ODA1)--(ODA2)` by clearing
one common denominator.  Since the atlas polytope is nonempty and rational,
such atlases always exist; `(ODA4)` says that a successful affine-support
witness must lie on an overlap face with a genuine mod-two denominator
obstruction.  Mere rationalizability of the tracial marginals is therefore
not enough to make the relaxation sound.

**Note (2026-08-22 audit).**  `linear-encoding-lcs-admits-odd-subset-cheats`
is OPEN again: its global statement fails for sources with non-extendable
local assignments (`odd-subset-relaxation-needs-local-extendability`);
any "encodings cannot create LCS hardness" / "dies by the odd-subset
cheat" reasoning here holds only under local extendability of the source.
