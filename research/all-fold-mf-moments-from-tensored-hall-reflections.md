---
rg: 2
id: all-fold-mf-moments-from-tensored-hall-reflections
kind: route
title: Tensor exact Hall reflections after adding canonical regular vertex blocks
target: leavitt-presentation-double-has-all-fold-mf-moments
requires:
  - hall-reflection-realizes-rank-one-restriction-instability
  - shulman-amalgam-mf-criterion
  - virtually-free-full-algebras-are-rfd
  - faithful-mf-models-realize-all-mf-traces
  - leavitt-presentation-double-fd-radical-is-fold-kernel
---

Choose increasing finite exhaustions `R_n subset K` and
`E_n subset F\{1}`.  The Hall-reflection theorem gives a permutation
representation `sigma_n^H:F->U(d_n)`, a base-coset rank-one projection
`p_n`, and `V_n^H=1-2p_n` such that

```text
[sigma_n^H(k),V_n^H]=0                  (k in R_n),
p_n perpendicular sigma_n^H(f_0)p_n sigma_n^H(f_0)^*.
                                                               (AFM4)
```

Residual finiteness of the free group gives a finite quotient separating
all of `E_n`.  Take its regular representation and repeat it until its total
dimension `e_n` is at least `d_n`; call the result `sigma_n^R`.  Put

```text
bar_sigma_n=sigma_n^H directSum sigma_n^R,
bar_V_n=V_n^H directSum 1_(e_n),
D_n=d_n+e_n.                                             (AFM5)
```

For `g in E_n`, the regular block has trace zero, hence

```text
|tr_(D_n)(bar_sigma_n(g))|<=d_n/D_n<=1/2.               (AFM6)
```

Also `(AFM4)` remains exact on `R_n`.  Choose integers `m_n->infinity` and
define

```text
sigma_n=bar_sigma_n^(tensor m_n),
V_n=bar_V_n^(tensor m_n),
v_n=sigma_n,                       u_n=V_n sigma_n V_n.  (AFM7)
```

Then `u_n,v_n` are exact representations of `F`, agree on every fixed
`k in K` eventually, and by `(AFM6)` both vertex characters converge to the
canonical character of `F`.

Let `q_n=sigma_n^H(f_0)p_n sigma_n^H(f_0)^*`.  On the one-particle space the
cross word is

```text
(bar_V_n bar_sigma_n(f_0) bar_V_n bar_sigma_n(f_0)^*)
 =1-2p_n-2q_n,                                           (AFM8)
```

because `p_n q_n=0`; it is the identity on the regular block.  Therefore
tensor multiplicativity of normalized trace gives `(AFM3)`.

The exact representations of the free product `F*F` defined by `(AFM7)`
kill every fixed amalgam relation in operator norm eventually.  They hence
define a star homomorphism from `C*(P)` to the norm matrix corona.  After a
subsequence on a countable dense star-subalgebra, their normalized traces
converge to an MF trace.  The choices of `m_n` listed after `(AFM3)` give any
prescribed `t in [0,1]` while `(AFM6)` keeps both vertex marginals canonical.

To impose swap symmetry, direct-sum each coordinate model with its
composition by the vertex swap.  The swapped word is `w^(-1)`, and `(AFM8)`
has real trace, so the value `t` is unchanged.  Finally
`faithful-mf-models-realize-all-mf-traces` adds a trace-negligible faithful
MF block, proving the asymptotically isometric assertion.  Equation `(AFM2)`
is the elementary identity

```text
tau_t((u_w-1)^*(u_w-1))=2-2 Re tau_t(w).
```

The exact-character-hull conclusion follows from the finite-dimensional
radical theorem.
