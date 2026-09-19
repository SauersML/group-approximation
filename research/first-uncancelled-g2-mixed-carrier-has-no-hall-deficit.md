---
rg: 2
id: first-uncancelled-g2-mixed-carrier-has-no-hall-deficit
kind: claim
title: The first uncancelled g2 mixed carrier has no Hall deficit
artifacts:
  - research/first-uncancelled-g2-mixed-carrier-rank-proof.md
distinct_from:
  first-g2-mixed-return-has-a-dihedral-half-absorber: that collects the two raw letters to the complementary-head root P; this keeps both raw entries in the carrier and leaves a g_2 target leg uncancelled.
  g2-one-raw-letter-sign-atlas-is-residually-finite: that permits only one raw orientation; this computes the first literal S/T product in both orders.
---

Use `U_2=g_2^2Ug_2^(-2)=x_(c_3,c_2)(T)` and put

```text
Y=VU_2
 =I+S E_(c_0,c_3)+T E_(c_3,c_2)+ST E_(c_0,c_2).       (UGM1)
```

Thus `Y` retains literal `S` and `T` entries; unlike its commutator,
it has not collected to a `q,qT` envelope. Let

```text
X_(sigma,tau)=G_(sigma,tau)Y G_(sigma,tau).
```

With `Z=I+qT E_(c_2,c_2)` from the first mixed-return theorem,

```text
X_(sigma,tau)^*X_(sigma,tau)
 =G_(sigma,tau)(1+Z)/2       if tau=+,
 =0                          if tau=-.                  (UGM2)
```

The reverse order `U_2V` has exactly the same initial-support table.
After the qutrit source cut `R=e_0+e_1`,

| raw order | sign `(sigma,tau)` | polar source rank |
|---|---|---:|
| `VU_2` or `U_2V` | `(+,+)` | `43/1152` |
| `VU_2` or `U_2V` | `(-,+)` | `7/192` |
| either | `(+,-)` or `(-,-)` | `0` |

Now leave a genuine target actor uncancelled. For every qutrit atom
`e_b` define

```text
T_(b,sigma,tau)
 =E e_b g_2 G_(sigma,tau)Y G_(sigma,tau)R.             (UGM3)
```

Its range is contained in `Ee_b`, whose trace is `1/18`. Left
multiplication by the contraction `Ee_b g_2` cannot increase the initial
polar rank, so `(UGM2)` gives

```text
tau(supp abs(T_(b,+,+))) <=43/1152 <1/18,
tau(supp abs(T_(b,-,+))) <=7/192   <1/18,
T_(b,sigma,-)=0.                                        (UGM4)
```

Therefore the shortest target-forcing operator which visibly contains an
uncancelled `g_2` leg and both raw orientations has no Hall excess in any
sign row. This is an exact support theorem in the canonical group trace,
not an energy comparison and not an appeal to a finite-dimensional
quotient.

The obstruction now starts at a longer alternating word: it must undo
the shared hidden sign `Z` while retaining separate `S` and `T` entries.
A two-letter `S/T` carrier, in either order, is exhausted by `(UGM2)`.
