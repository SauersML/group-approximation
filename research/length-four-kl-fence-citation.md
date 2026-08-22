---
rg: 2
id: length-four-kl-fence-citation
kind: route
title: Apply the universal length-three and length-four equation theorems
target: length-four-kl-fence-for-leavitt-equations
requires: []
---

Howie, *The solution of length three equations over groups*, Proc. Edinburgh
Math. Soc. **26** (1983), 89--96, proves that every equation of variable
length three has a solution over an arbitrary coefficient group.  Edjvet and
Howie, *The solution of length four equations over groups*, Trans. Amer. Math.
Soc. **326** (1991), 345--369, DOI
`10.1090/S0002-9947-1991-1002920-5`, prove the Kervaire--Laudenbach
injectivity statement whenever the sum of the absolute values of the variable
exponents is four.  Length one and two reduce directly to root adjunction and
an HNN/amalgam normal form (and are also subsumed by the standard low-length
discussion in those papers).

These are theorems over **every** group.  Apply them to
`G=L_(F_2)(1,2)^x`.  Their conclusion is exactly injectivity of

```text
G -> (G*<t>)/<<w>>,
```

so it is unaffected by whether the coefficient support lies in a proper
subgroup or generates `G` itself.

For the boundary calculation, each occurrence contributes `+1` or `-1`
after powers are expanded, hence `deg_t(w)` and `ell_t(w)` have the same
parity.  At length five, nonsingularity leaves absolute degrees `1,3,5`.
Absolute degree five means all signs agree; Levin's positive-equation theorem
(*Solutions of equations over groups*, Bull. Amer. Math. Soc. **68** (1962),
603--604) gives an overgroup solution, so only the `4+1` and `3+2`
mixed-sign types remain.

Klyachko--Thom, *New topological methods to solve equations over groups*,
Algebr. Geom. Topol. **17** (2017), 331--353, DOI
`10.2140/agt.2017.17.331`, Remark 1.2, independently records the length-three
theorem and the Edjvet--Howie length-four theorem.  It lists length-five work
only as a similar restricted result, so this route deliberately makes no
universal length-five claim.
