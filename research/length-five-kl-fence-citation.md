---
rg: 2
id: length-five-kl-fence-citation
kind: route
title: Apply Evangelidou's universal solution theorem for length-five equations
target: length-five-kl-fence-for-leavitt-equations
requires: []
---

Evangelidou, *The Solution of Length Five Equations Over Groups*,
Communications in Algebra **35** (2007), 1914--1948, DOI
`10.1080/00927870701247039`, proves that every nonsingular one-variable
equation of variable length five has a solution over an arbitrary coefficient
group.  The published abstract is explicit: the article removes the earlier
coefficient restrictions and “settles the KL conjecture for equations of
length five.”

The complete precursor thesis, *Equations of length five over groups*
(University of Nottingham, 2002), supplies the relative-diagram proof.  It
reduces, up to cyclic permutation and inversion, to

```text
r_0=atbtctdtet,
r_1=atbtctdtet^(-1),
r_2=atbtctdt^(-1)et^(-1),
r_3=atbtct^(-1)dtet^(-1).
```

Levin settles `r_0`.  The thesis's Chapters 5--8 remove the residual
coefficient restrictions for `r_1,r_2,r_3`; its final curvature calculation
proves that the required spherical counterexample diagram cannot exist.
Thus the coefficient map is injective for both the `++++-` and `+++--`
patterns, with no condition on the coefficient subgroup.

Together with Howie, *The solution of length three equations over groups*,
Proc. Edinburgh Math. Soc. **26** (1983), 89--96, and Edjvet--Howie,
*The solution of length four equations over groups*, Trans. Amer. Math. Soc.
**326** (1991), 345--369, this covers every nonsingular variable length at
most five.  Klyachko--Thom, *New topological methods to solve equations over
groups*, Algebr. Geom. Topol. **17** (2017), Remark 1.2, also records the
length-five result.

For the new boundary, each expanded occurrence contributes `+1` or `-1`, so
`deg_t(w)` and `ell_t(w)` have the same parity.  At length six,
nonsingularity leaves absolute degrees `2,4,6`; Levin's positive-equation
theorem removes absolute degree six.  The remaining distributions are exactly
`5+1` and `4+2`.  Ivanov--Klyachko's length-six result assumes the coefficient
group is torsion-free and therefore does not apply to `G`, which contains the
elementary involutions `x_ij(1)`.

