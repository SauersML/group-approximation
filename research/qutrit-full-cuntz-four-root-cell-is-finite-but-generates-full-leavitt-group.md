---
rg: 2
id: qutrit-full-cuntz-four-root-cell-is-finite-but-generates-full-leavitt-group
kind: claim
title: The first full-Cuntz qutrit cell is finite but its scalar closure is the full Leavitt group
artifacts:
  - research/qutrit-full-cuntz-four-root-cell-proof.md
distinct_from:
  qutrit-first-infinite-prefix-holonomy-is-dihedral-amenable: that uses only the positive free subalgebra and yields a residually finite concrete subgroup; this consumes both negative prefix letters and the completeness relation s0t0+s1t1=1.
  positive-steinberg-qutrit-bridges-are-central-by-finite: that treats arbitrary roots in one positive root direction and proves finiteness abstractly; this computes the exact first four-root Cuntz cell, its qutrit atom table, and the fact that scalar conjugation makes it generate the entire elementary group.
  universal-leavitt-el4-nonsofic: that proves nonsoficity of the global elementary group; this identifies the smallest local Cuntz cancellation cell and shows why its finite-amalgam shadow cannot see that global obstruction.
---

Keep `h=J^2Z` and choose, in its fixed block, distinct coordinates
`i,j,k` with `i,k` in trivial `C`-summands and `j` in the
nontrivial `C`-type killed by `h`. Put

```text
U_r=x_(ij)(s_r),       V_r=x_(jk)(t_r),       r=0,1,
Z_(rs)=[U_r,V_s]=x_(ik)(s_r t_s).                       (QFC1)
```

All four roots centralize `h`. The four `Z_(rs)` are central in the
group `N=<U_0,U_1,V_0,V_1>`, and the full Cuntz relation gives the
exact scalar return

```text
Z_(00) Z_(11)=x_(ik)(s_0t_0+s_1t_1)=x_(ik)(1)=:A.      (QFC2)
```

The group `N` is finite of order

```text
|N|=2^(2+2+4)=256.                                      (QFC3)
```

It is the two-step exponent-four packet with two-dimensional upper and
lower root spaces and four-dimensional central matrix-unit space. Its
intersection with `K=GL_28(F_2)` is exactly `<A>`.

For each of the four noncentral roots `v=U_r,V_r`,

```text
C intersect vCv^(-1)=<h>,
p_(alpha',beta') v p_(alpha,beta) !=0
 iff 2alpha'+beta'=2alpha+beta,
||p_(alpha',beta') v p_(alpha,beta)||_2^2=1/27.         (QFC4)
```

Every central return `Z_(rs)` acts on the two trivial coordinates and
commutes with `C`. Thus the completeness relation `(QFC2)` couples the
two prefix branches algebraically but does not orient the three equal
character cells in an `h`-fibre. The uniform nine-character weight
vector remains feasible.

There is no intermediate scalar-closed subgroup. Constant Weyl
conjugation moves each of `U_0,U_1,V_0,V_1` to every ordered root
position; root addition and Steinberg commutators then generate every
coefficient in `L=L_(F_2)(1,2)`. Hence

```text
<K,N>=EL_28(L).                                         (QFC5)
```

At the same time all relations visible inside this one cell have the
finite graph-of-groups cover

```text
K *_(<h,A>) (<h> times N) -> EL_28(L).                  (QFC6)
```

Both vertices and the edge are finite, so the group on the left is
virtually free, residually finite, sofic, and hyperlinear. Its canonical
microstates retain `tau(q)=1/3`, all nine weights `1/9`, the atom
table `(QFC4)`, and the nontrivial scalar return `A`. The map in
`(QFC6)` has nontrivial kernel; the established nonsoficity of the
target already forbids injectivity.

Therefore the first relation using the full Cuntz sum reaches the global
Leavitt candidate but supplies no local normalized-HS trace imbalance.
The next load-bearing object is not a fifth root in the same cell. It is
a concrete kernel relation between two distinct `K`-conjugates of this
cell whose finite-amalgam regular model cannot satisfy the required
qutrit occurrence typing.
