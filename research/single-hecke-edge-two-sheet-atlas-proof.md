---
rg: 2
id: single-hecke-edge-two-sheet-atlas-proof
kind: route
title: Reduce away from p and tensor the denominator automorphism with a sheet flip
target: single-hecke-edge-has-exact-two-sheet-atlases
requires: []
---

Let

```text
Q_m=SL_3(Z/mZ),          q_m:Lambda->Q_m.
```

Reduction is onto.  Since `p` is invertible modulo `m`, the matrix `h` has
a reduction `hbar in Q_m`.  Conjugation by `hbar` defines an automorphism

```text
alpha=Ad(hbar):Q_m->Q_m,                                  (HAP1)
```

and for every `c in I`,

```text
alpha(q_m(c))=q_m(h c h^(-1))=q_m(phi(c)).                (HAP2)
```

On `Omega_m=Q_m x Z/2`, define

```text
c.(x,j)=(q_m(c)x,j),
t.(x,j)=(alpha(x),j+1).                                   (HAP3)
```

These are permutations.  For `c in I`, direct calculation gives

```text
t c t^(-1).(x,j)
  =(alpha(q_m(c))x,j)
  =(q_m(phi(c))x,j)
  =phi(c).(x,j).                                          (HAP4)
```

Hence `(HAP3)` extends to an exact action of the HNN group `E_h` by its
presentation.  The sheet map `ell(x,j)=j` is unchanged by every element of
`Lambda` and changed by `t` at every point, proving `(HEA3)`.

Finally, `hbar` belongs to `q_m(Lambda)=Q_m`.  Thus on the `Q_m` coordinate
the denominator automorphism is already implemented by the finite image of
`Lambda`; the only new datum is the sheet flip.  If `(HAP3)` extended from
`E_h` to an exact action of `Gamma` with `t` representing `h`, permutation
co-density would force the full image of `Gamma` to equal the image of
`Lambda`, which preserves each sheet, a contradiction.  Therefore precisely
the full-`Gamma` relations omitted by the one-edge HNN presentation must
destroy the model.
