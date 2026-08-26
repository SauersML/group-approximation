---
rg: 2
id: unbalanced-torus-extracts-near-central-denominator-coordinate
kind: claim
title: The unbalanced torus word extracts every near-central denominator coordinate
distinct_from:
  unbalanced-torus-relator-closes-product-projective-sector: that assumes one displayed tensor-product multiplicity factor; this treats an arbitrary finite-dimensional exact ambient representation, extracts its commutant coordinate from the fixed overlap by the Kazhdan projection, and leaves only the ambient-extension outlier.
  sl3-projective-transfer-enemy-dichotomy: that separates lattice-correctable actors from inner-adjoint outliers and then extracts denominator-primary conductor mass; this refines the case in which the lattice tuple is close to the restriction of an exact ambient actor, without asserting that every dyadic lattice correction extends to the ambient group.
  unbalanced-torus-word-localizes-britton-leak: that localizes a canonical HNN stable-letter leak on two negative roots for an arbitrary actor; this gives a projective-transfer inequality whenever the denominator's relative coordinate is nearly central for one exact ambient reference actor.
  sl3-odd-correctable-sector-has-uniform-projective-modulus: that gives an existential modulus by an ultraproduct contradiction for all coprime lattice corrections; this gives a direct finite-dimensional inequality, identifies the fixed overlap relations which extract the coordinate, and allows arbitrary blockwise multiplicities from the outset.
---

Put

```text
C=SL_3(Z),       A=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)),
```

and fix a symmetric Kazhdan generating set `S` of `C`, with Kazhdan
constant `kappa>0`.  Put

```text
C_+=C intersect h C h^(-1)
```

and fix a symmetric Kazhdan generating set `S_+` of this finite-index
subgroup, with constant `kappa_+>0`.  Let `R_tor` be the fixed unbalanced
word from `two-torus-closures-detect-denominator-multiplicity`.  There are
constants `K,C_0<infinity`, depending only on the fixed words and on
`kappa_+`, with the following property.

Let `sigma:A->U(d)` be any exact finite-dimensional representation and let
`H,U in U(d)` be arbitrary.  Define the **relative denominator coordinate**

```text
W=H sigma(h)^*,
a_+(W)=sum_(c in S_+)||[W,sigma(c)]||_2^2,
q_C(U)=sum_(s in S)(1-|tr([U,sigma(s)])|^2),
eta=||ev_(sigma|_C,H)(R_tor)-I||_2.                    (NCD1)
```

Then

```text
1-|tr([U,H])|^2
 <= K q_C(U)+C_0 eta^2+C_0 a_+(W).                    (NCD2)
```

The statement is basis free and allows arbitrary isotypic multiplicities.
Indeed, after a Wedderburn decomposition of `sigma`, every genuine
commutant coordinate has the form

```text
V=direct-sum_alpha (V_alpha tensor I_(K_alpha)),        (NCD3)
```

with unrelated unitaries `V_alpha` on the different multiplicity spaces.
Thus `(NCD2)` strictly contains the single tensor factor in the original
product-sector theorem.

The overlap term is not an additional hypothesis for approximate ambient
actors.  For `c in S_+`, put `c'=h^(-1)c h in C`.  The fixed ambient
relation

```text
h c' h^(-1)=c                                           (NCD4)
```

says exactly that `W` centralizes `sigma(c)`, up to the ambient presentation
defect and the distance from the approximate lattice packet to `sigma`.
All words here are fixed, so the resulting modulus is dimension independent.

Consequently, suppose an approximate actor `(X,H)` has presentation defect
`delta`, its lattice generators are within `xi` of `sigma(S)`, and its
projective lattice energy is `q`.  Fixed-word telescoping in `(NCD2)` gives

```text
1-|tr([U,H])|^2 <=Omega(delta+xi+q),                    (NCD5)
```

for a dimension-independent modulus `Omega(t)->0`.  In particular, along a
projective-transfer enemy, the lattice restriction cannot approach the
restriction of exact same-dimensional ambient representations:

```text
liminf_n inf_(sigma:A->U(d_n))
 max_(s in S)||X_(n,s)-sigma(s)||_2 > 0.                (NCD6)
```

Thus the unbalanced relation closes the entire ambient-extendable
correction sector, not merely an exposed tensor multiplicity.  The sole
residual is the **ambient-extension outlier** `(NCD6)`.  The claim does not
identify a merely lattice-correctable dyadic representation with an ambient
representation; that would erase the genuine conductor obstruction isolated
elsewhere.
