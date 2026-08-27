---
rg: 2
id: compressed-antiphase-menu-implies-btb-escape
kind: claim
title: A fixed compressed-antiphase menu forces one protected BTB branch to escape
distinct_from:
  pairwise-antiphase-covariance-controls-cross-gram: That bounds pairwise Gram energy from supplied opposite phases; this combines it with BTB source density and corner capacity to obtain one fixed-fraction escape.
  literal-antiphase-branches-recreate-regular-character-packing: That rules out implementing the hypotheses by full literal source conjugacy; this deliberately assumes only compressed covariance on the analytic reached carrier.
  canonical-btb-finite-depth-escape-tree: That asks directly for one escaping word; this reduces it to a finite menu of compressed pairwise phase tests and permits the escaping branch to be selected adaptively.
---

**ESTABLISHED CONDITIONAL COMPILER.**  At one reached node use the notation
of `(CBR1)--(CBR2)`.  Put

```text
q=tau(Q),             a=tau(A),             r=tau(F),
r>=(1/18)a-O(sqrt(E)),
a>=(beta/M)q-O(sqrt(E)).                               (CAM1)
```

Choose once and for all an integer

```text
L beta/(18M)>=4.                                      (CAM2)
```

Suppose a finite extension supplies branch words `u_1,...,u_L` preserving
the common marked capacity and, for every `k<l`, a target involution `R_kl`
reduced by `Q`.  Define the **compressed branch contractions**

```text
T_k=Q u_k F.                                           (CAM3)
```

Assume only the compressed opposite-phase estimate

```text
sum_(k<l) (||R_kl T_k-T_k||_2^2
          +||R_kl T_l+T_l||_2^2)
 <=C_pair E.                                          (CAM4)
```

Then at least one branch has fixed escape:

```text
tau(Q u_k F u_k^* Q)
 <=tau(F)-(1/36)tau(A)+C_esc sqrt(E).                  (CAM5)
```

Consequently `(CAM4)` supplies `(CBR3)` with `eta=1/36`; enlarge the finite
adaptive decision tree by the fixed `L`-element branch menu and use the
escaping branch at each reached node.

## Proof

Let

```text
m_k=||T_k||_2^2=tau(Q u_k F u_k^* Q),
ell_k=r-m_k,        ell=sum_k ell_k,
S=sum_k m_k=Lr-ell.                                  (CAM6)
```

The pairwise-antiphase inequality applied to `(CAM4)` gives

```text
O=sum_(k!=l)||T_l^*T_k||_2^2<=C_pair E.               (CAM7)
```

All `T_k` have range in `Q`.  The contraction capacity inequality therefore
gives

```text
O>=S^2/q-S.                                           (CAM8)
```

Solving the quadratic and using `sqrt(q^2+4qO)<=q+2O` yields

```text
S<=q+O,
ell>=Lr-q-O.                                          (CAM9)
```

Ignoring the fixed `O(sqrt(E))` correction for one line, `(CAM1)--(CAM2)`
give `Lr>=4q`, hence

```text
max_k ell_k>=ell/L>=r-q/L-O/L
                         >=(3/4)r-O/L
                         >=a/24-O(sqrt(E)).            (CAM10)
```

Absorbing packet correction and the harmless stronger constant into
`1/36` proves `(CAM5)`.  In the canonical BTB route every reached carrier
has `q>=1/8-o(1)`, so division by the capacity in the quadratic estimate
does not create a dimension- or node-dependent constant.

The exact perfect marked model is compatible with the analytic hypothesis:
there `F=0`, so every term in `(CAM4)` vanishes regardless of the auxiliary
involutions.  What remains open is not the capacity calculation but an
ordinary finite presentation which implies the **compressed** estimate
`(CAM4)` without implying the literal full-source conjugacies `(LAP2)`.

DERIVATION
compressed-antiphase-btb-capacity-proof

