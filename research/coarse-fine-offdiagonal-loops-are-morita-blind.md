---
rg: 2
id: coarse-fine-offdiagonal-loops-are-morita-blind
kind: claim
title: Every ordinary coarse-fine off-diagonal path loop is blind to the additive packet identity
artifacts:
  - experiments/coarse_fine_offdiagonal_loop_audit.py
distinct_from:
  mixed-steinberg-loops-admit-morita-rectangular-model: that gives the general typed-category fence for previously named rank-five and rank-six loops; this writes the complete depth-one/depth-two bridge chart, identifies its shortest mixed loops, and computes the missing packet-identity norm exactly.
  literal-prefix-three-root-swap-retains-typed-carriers: that audits one stabilized Whitehead actuator between designated minimal corners; this permits every crossed bridge between the two complete prefix packets and every loop obtained by pasting their ordinary off-diagonal triangles.
  support-return-odd-loops-do-not-imply-atomic-return: that supplies a finite marked Pauli model for two authenticated support-return occurrences; this isolates the additive firewall before any support reflection is introduced.
---

**ESTABLISHED, with a sharp language fence.**  Put

```text
e_ij=s_i t_j,                    i,j in {0,1},
f_uv=s_u t_v,                    |u|=|v|=2,
x_(u,i)=s_u t_i,
y_(i,u)=s_i t_u.                                      (CFL1)
```

The shortest ordinary paths which enter the other prefix packet and return
are the three-factor identities

```text
x_(u,i) e_ij y_(j,v)=f_uv,
y_(i,u) f_uv x_(v,j)=e_ij.                            (CFL2)
```

The two-factor turns are

```text
y_(i,u)x_(v,j)=delta_(u,v)e_ij,
x_(u,i)y_(j,v)=delta_(i,j)f_uv.                       (CFL3)
```

Consequently every closed word obtained by pasting `(CFL2)--(CFL3)`, packet
matrix-unit triangles, distant-root commutations and their ordinary
non-opposite Steinberg commutator realizations reduces to one typed matrix
unit or to zero.  Such a word tests composition, but never compares the two
object identities

```text
P_1=sum_i e_ii,                 P_2=sum_(|u|=2) f_uu. (CFL4)
```

There is an exact finite countermodel to any fixed family of these loops.
Take six one-dimensional objects over `F_2`, two coarse objects and four fine
objects.  Realize `e`, `f`, `x`, and `y` as the corresponding matrix units in
`M_6(F_2)`.  Equations `(CFL2)--(CFL3)` and every pasted loop hold exactly,
whereas on the common complex coordinate space

```text
P_1=diag(1,1,0,0,0,0),
P_2=diag(0,0,1,1,1,1),
||P_1-P_2||_op=1.                                     (CFL5)
```

Placing these coefficient arrows in distinct external Steinberg root
positions gives a finite block-transvection group.  Its regular unitary
representation realizes the same ordinary root-word table, and any chosen
nonzero elementary transvection used as the marked root survives.  Thus the
fence applies to exact marked finite unitary models, not only to an abstract
diagram of vector spaces.

The scope is essential.  This does not model the full binary-Leavitt
Steinberg presentation: a literal root-addition occurrence identifying the
two sums in `(CFL4)`, or a wordized spectral support incidence for that
occurrence, defeats the typed model.  It proves exactly that **no fixed
family made only from ordinary off-diagonal multiplication/commutator loops
through the two prefix packets can control**
`||P_1-P_2||_op`.  A successful operator-norm row must add the coefficient
completeness occurrence on the selected marked carrier; lengthening or
reassociating the off-diagonal loop family cannot do so.

DERIVATION
coarse-fine-offdiagonal-loop-morita-proof
