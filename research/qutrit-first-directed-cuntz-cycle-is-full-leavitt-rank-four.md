---
rg: 2
id: qutrit-first-directed-cuntz-cycle-is-full-leavitt-rank-four
kind: claim
title: The first directed Cuntz cycle reaches the full rank-four Leavitt group
artifacts:
  - research/qutrit-directed-cuntz-cycle-rank-four-proof.md
distinct_from:
  qutrit-first-nonparallel-cuntz-return-chain-is-finite: that proves every acyclic return chain is finite; this adds one scalar coordinate cycle and identifies the resulting concrete subgroup.
  qutrit-four-root-cell-finite-but-generates-full-leavitt: that needs the entire scalar group K as an external closure; this shows one explicit four-cycle permutation and the two scalar returns already generate the required local GL4.
  matched-leavitt-opposite-root-qutrit-bridge-is-gl28: that uses one matched leaf chart and obtains a finite scalar group; this uses both binary branches, closes a coordinate cycle, and obtains the full infinite Leavitt coefficient group.
---

Use the four-coordinate selector chain `i->j->k->ell` and its finite
group `M` from [[qutrit-first-nonparallel-cuntz-return-chain-is-finite]].
Recall its scalar returns

```text
A=x_(ik)(1),                 B=x_(j,ell)(1).
```

Let `P` be the scalar coordinate cycle

```text
P=(i j ell k).
```

Then

```text
K_0=<A,B,P>=GL_4(F_2)                                   (QCY1)
```

on these four coordinates. The `P`-orbits of `A` and `B` are the
transvections in the two orientations around the four-cycle; their
commutators give every constant root.

Since `M` already contains roots with coefficients
`s_0,s_1,t_0,t_1`, scalar conjugation and Steinberg commutators now give

```text
<M,P>=EL_4(L_(F_2)(1,2))                                (QCY2)
```

in the active block. Thus the first directed coordinate cycle is not an
intermediate residually finite chart: it reaches the full rank-four
Leavitt elementary group, which is nonsofic and not residually finite.
Its hyperlinearity remains the ambient open problem.

The shortest cross-cycle selector relation is explicit. For

```text
U_r=x_(ij)(s_r),             V_s=x_(jk)(t_s),
D=P^2 A P^(-2)=x_(ell,j)(1),
```

one has

```text
[P V_s P^(-1),U_r]=D^(delta_(sr)).                      (QCY3)
```

Indeed `PV_sP^(-1)=x_(ell,i)(t_s)` and
`t_ss_r=delta_(sr)`. The two diagonal rows return the same scalar
multiplicity involution `D`; the two cross rows commute.

Relation `(QCY3)` alone still has a finite packet. The four noncentral
roots in it generate a group `Q` with normal form

```text
X(t)Y(s)D^epsilon,
t in span{t_0,t_1}, s in span{s_0,s_1}, epsilon in F_2,
```

so `|Q|=2^5=32`. Every `X(t_s)` and `Y(s_r)` has the complete
three-by-three `h`-fibre qutrit graph with squared block norm `1/27`,
while `D` commutes with `C`. Thus the first cycle row has an exact
regular finite-dimensional model with all nine qutrit weights `1/9`
and creates no trace imbalance.

The hard boundary is therefore collective. The finite scalar/qutrit
vertex and the finite acyclic cell have a virtually free amalgam shadow,
but imposing their complete `P`-covariance quotient gives `EL_4(L)`.
No single delta row detects that quotient in normalized Hilbert--Schmidt
norm. The next load-bearing task is a bounded family of cross-cycle
relations whose common polar or character support cannot be realized in
the 32-element selector packet, not another isolated inverse-prefix
commutator.
