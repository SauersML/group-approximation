---
rg: 2
id: qutrit-first-mixed-cycle-cell-is-finite
kind: claim
title: The first mixed negative-letter cycle cell is still finite
artifacts:
  - research/qutrit-first-mixed-cycle-cell-finite-proof.md
distinct_from:
  qutrit-first-cycle-phase-flip-is-a-finite-amalgam: that handles the complete-to-diagonal covariance of one positive root family; this adds a negative root from the preceding actor row and uses the full Cuntz sum.
  qutrit-four-root-cell-finite-but-generates-full-leavitt: that studies one three-coordinate cell before the directed actor closure; this identifies the first cell genuinely shared by two distinct actor translates and computes its alternating qutrit types.
---

For cyclic coordinates `c_a` and roots `X_(a,s),Y_(a,r),D_a` from
[[qutrit-first-cycle-phase-flip-is-a-finite-amalgam]], the first
cross-row commutator is

```text
[X_(a,s),Y_(a+1,r)]
 =x_(c_(a+1),c_a)(s_rt_s).                              (QMX1)
```

Hence the two matched branches satisfy

```text
product_(r=0)^1 [X_(a,r),Y_(a+1,r)]
 =x_(c_(a+1),c_a)(s_0t_0+s_1t_1)
 =D_(a+3).                                               (QMX2)
```

This is the first actor-shared relation that uses a negative prefix and
the additive Cuntz identity. Nevertheless the four roots in `(QMX2)`
generate a finite group `N_a` of order `256`. It has the unique normal
form

```text
X(t)Y(s)Z(w),
t in span{t_0,t_1}, s in span{s_0,s_1},
w in span{s_rt_s:r,s in {0,1}}.                         (QMX3)
```

The qutrit phase table alternates with the actor parity:

```text
a parity       X_(a,s)       Y_(a+1,r)      D_(a+3)
even           complete      diagonal         complete
odd            complete      complete         diagonal. (QMX4)
```

More strongly, adjoining the whole finite qutrit torus does not make this
cell infinite:

```text
<C,N_a> is finite.                                      (QMX5)
```

Indeed the three coordinate modules form an acyclic chain. Taking the
finite `C`-orbit span of the three root spaces produces a
finite-dimensional strictly upper triangular `F_2`-algebra, normalized
by `C`, and `<C,N_a>` lies in its finite algebra group semidirect `C`.

Thus `(QMX1)--(QMX4)` have a literal exact finite regular model with all
nine `C`-character weights `1/9`. The first mixed negative-letter
relation does not create a normalized-Hilbert--Schmidt defect. Any live
cycle obstruction must combine at least two such cells so that their
coordinate incidence is genuinely cyclic; a single actor-shared Cuntz
return is still an acyclic finite packet.
