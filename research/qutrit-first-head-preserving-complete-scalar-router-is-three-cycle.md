---
rg: 2
id: qutrit-first-head-preserving-complete-scalar-router-is-three-cycle
kind: claim
title: The first head-preserving complete scalar router is a three-cycle with a finite head envelope
artifacts:
  - research/qutrit-head-preserving-three-cycle-router-proof.md
distinct_from:
  qutrit-third-cell-head-selector-is-h-centralizer-zero: that proves every three-cell Leavitt word stays diagonal on the proper qutrit row; this adds the smallest scalar actor that really crosses that row.
  qutrit-full-leavitt-prefix-conjugator-realizes-phase-star: that builds a nonconstant Leavitt conjugator with a three-to-one phase star and forced leakage; this uses one constant scalar three-cycle, preserves the named Jacobson head, and computes its much smaller complete-graph compression.
  qutrit-head-only-overlap-envelope-is-finite: that closes the full scalar group with arbitrary head roots; this locates the minimal support of a nonzero head-preserving qutrit arrow and identifies its exact finite failure mode.
---

In the simultaneous `C=<J,Z>` decomposition over `F_2` write

```text
F_2^28=U_10 direct-sum W_0^3 direct-sum W_1^3 direct-sum W_2^3,
type(W_0)=[1,0],   type(W_1)=[1,-1],   type(W_2)=[1,-2].
                                                               (QSA1)
```

For `h=J^2Z`, the `h`-fixed block is `U_10 direct-sum W_2^3`.
Choose the active trivial coordinate `c_0` away from the support of

```text
H=x_(c_2,c_1)(Q_0),       Q_0=1-s_0t_0,
E=(1-H)/2,
```

and choose nonzero coordinate vectors `d_0` and `d_1` in one copy of
`W_0` and one copy of `W_1`. Let `g` be the scalar coordinate
three-cycle

```text
g=(c_0 d_0 d_1) in GL_28(F_2).                           (QSA2)
```

Then

```text
[g,H]=1,              [g,h]!=1,
C intersect gCg^(-1)={1}.                               (QSA3)
```

Thus `g` is the first support-minimal scalar actor which both touches the
active block without touching the head and gives a complete qutrit graph.
For the selected atoms `e_a=z_(1,a)`,

```text
||e_b g e_a||_2^2=1/81                       for all a,b,
||e_b g E e_a||_2^2=1/162                    for all a,b. (QSA4)
```

With `R=e_0+e_1`, the desired arrow is genuinely nonzero:

```text
A=e_2 g E R !=0,             ||A||_2^2=1/81.             (QSA5)
```

But it is not a Hall selector. Its source and target capacities are

```text
tau(ER)=1/9,                 tau(Ee_2)=1/18,             (QSA6)
```

and the source support of the polar of `A` has trace at most `1/18`.
At least `1/18` of the proposed source carrier is therefore absent rather
than transported.

This failure is exact in finite dimension. The head commutes with the
finite scalar group `<C,g>` and has trivial intersection with it, so

```text
<C,g,H>=<C,g> times <H>                                  (QSA7)
```

is finite. Equivalently it lies in the head algebra envelope

```text
EL_28(F_2[Q_0]) isomorphic to
GL_28(F_2) times GL_28(F_2).                             (QSA8)
```

Its regular representation realizes `(QSA3)--(QSA6)` exactly.

The support-three threshold is sharp. A head-disjoint transposition from
`c_0` to one moving type has order-three intersection with `C` and is
diagonal on `e_0,e_1,e_2`. A transposition between `W_0` and `W_1` can
have trivial intersection, but is disjoint from the entire `h`-fixed
Leavitt core. The cycle `(QSA2)` is the first actor doing both jobs.

Finally `<G_3,C,g>` still contains the full nonsofic
`G_3=EL_4(L)` core, but it is not `EL_28(L)`: it preserves the proper
`C`-invariant sum of the active support with the two chosen moving
summands. The single actor does not reach the untouched multiplicity
copies. Hence a viable next candidate needs either a second scalar actor
closing those copies or a head-touching actor whose conjugated
`Q_0`-root supplies a nonfinite return.
