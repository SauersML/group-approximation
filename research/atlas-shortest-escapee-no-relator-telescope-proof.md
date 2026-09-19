---
rg: 2
id: atlas-shortest-escapee-no-relator-telescope-proof
kind: route
title: Evaluate both dangerous commutators in the rank-five elementary model
target: atlas-shortest-escapee-has-no-relator-telescope
requires:
  - atlas-shortest-escapee-literal-control-firewall
  - atlas-steinberg-rank-five-translation
---

# Survival of the two dangerous commutators

The exact rank-five dictionary expansions are

```text
x_15(1)=(1,8461)=a_1,
x_35(1)=(2,8461)=a_2,
x_53(1)=(2,8621)=b_2.                                 (NRP1)
```

The same dictionary gives

```text
x_13(1)=(1,8461)(2,8621)(1,8461)(2,8621)
       =[a_1,b_2],                                    (NRP2)
```

because `a` and `b` are involutions.  Thus `r_b` maps to `x_13(1)` in the
canonical Leavitt quotient.

For the other term, the matrix identity `c=aba` inside the second chart and
`(NRP1)` give

```text
c_2=x_35(1)x_53(1)x_35(1)=:n_35.                     (NRP3)
```

In the rank-five elementary matrix model, the restriction of `n_35` to
coordinates `3,5` is

```text
[[1,1],[0,1]] [[1,0],[1,1]] [[1,1],[0,1]] = [[0,1],[1,0]],
```

so `n_35` is the involution swapping those two coordinates.  It fixes
coordinate `1`, and therefore

```text
n_35 x_15(1)n_35=x_13(1).                             (NRP4)
```

Since `x_15(1)` and `n_35` are involutions,

```text
r_c=[x_15(1),n_35]
   =x_15(1)n_35x_15(1)n_35
   =x_15(1)x_13(1),                                  (NRP5)
```

which proves `(NRT3)`.

Under the prefix-code identification of `M_5(L)` with the binary Leavitt
algebra,

```text
x_13(1)=I+E_13,
x_15(1)x_13(1)=I+E_15+E_13,                          (NRP6)
```

because `E_15 E_13=0`.  Both are nonidentity: their displayed off-diagonal
matrix entries are nonzero.  Equivalently, multiplying `E_13` on the left by
`E_31` isolates `E_33`, so the first difference cannot vanish; the distinct
`(1,5)` and `(1,3)` matrix entries prevent cancellation in the second.

Every translated Steinberg and involutivity relator in `T_St` was constructed
in the kernel of this canonical map.  Hence `<<T_St>>` lies in its kernel,
whereas `(NRP6)` shows that `r_b` and `r_c` do not.  This proves `(NRT2)`.

Finally, membership in the normal closure of a set of relators is equivalent
to having a finite expression as a product of conjugates of those relators
and their inverses.  Thus `(NRT2)` forbids `(NRT4)`.  Evaluating such an
expression in unitaries would give the standard Hilbert--Schmidt defect
telescope, so no exact relator-factorization proof can charge either of the
two dangerous terms.
