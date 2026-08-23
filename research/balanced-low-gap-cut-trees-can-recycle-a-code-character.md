---
rg: 2
id: balanced-low-gap-cut-trees-can-recycle-a-code-character
kind: claim
title: Balanced low-gap cut trees can recycle an entire exact code character
distinct_from:
  small-cut-hs-does-not-control-terminal-operator: that uses disjoint two-dimensional swaps with tiny global cuts; this strengthens the obstruction to balanced half-cuts coming from bounded low-adjoint-energy spectral witnesses while all parity and complete-pair relations are exact.
  terminal-cut-tree-carleson-controls-aggregate-offdiagonal: that asks for a selected terminal tree with a Carleson invariant; this proves that balanced relations and local low-gap admissibility alone cannot provide that invariant.
---

ESTABLISHED FIREWALL.  Let `C <= F_2^L` be a binary linear code and let
`0 != c in C` have relative weight

```text
delta=|supp(c)|/L>0.
```

For every `rho>0` there are a finite tracial matrix algebra, an exact
commuting code-reflection tuple `(B_i)_(i=1)^L`, and a finite rooted binary
tree of **trace-halving** spectral cuts such that:

1. every cut is the positive spectral projection of a selfadjoint witness
   `x` with normalized corner trace zero, `||x||_2=||x||_op=1`;
2. at every node its normalized adjoint row energy obeys

   ```text
   (1/L)sum_i||[eB_ie,x]||_(2,e)^2 <=4 delta rho;       (BRC1)
   ```

   the unnormalized sum can likewise be made arbitrarily small by replacing
   `rho` by `rho/L`;
3. all original parity relations and all complete-pair commutators vanish
   exactly;
4. for the terminal PVM `F`,

   ```text
   Phi_F(B_i)=0  if c_i=1,       Phi_F(B_i)=I if c_i=0. (BRC2)
   ```

Consequently, with `O_i=B_i-Phi_F(B_i)` and
`A=L^(-1)sum_iO_i^2`,

```text
D=L^(-1)sum_i||O_i||_2^2=delta,
A=delta I,
L^(-1)sum_i tau(O_i^4)=delta,
tau(A^2)=delta^2.                                      (BRC3)
```

Thus neither the diagonal fourth moments nor the row square function gain
an `o(1)` factor over `D`, although every retained cut is balanced and has
arbitrarily small relative low-gap energy.  With the convention
`sgn(0)=1`, the terminal signed tuple is the all-identity code character,
so its parity and complete-pair energy is again exactly zero.  The recycling
is invisible to every balanced group relation: it changes the multiplicity
of the original nonzero character into the trivial character.

The conclusion is a no-go only for arguments using **local low-gap cut
admissibility plus balanced relation energy**.  It does not say that every
possible cut-selection rule is bad: the original exact tuple also has
zero-boundary character cuts.  A valid terminal Carleson theorem must add a
global selection/minimization rule or a trace/character-multiplicity
Lyapunov invariant which selects those zero-boundary cuts and forbids the
tree above.  A third possible escape is to exploit the free sign on the
terminal zero kernels and choose it coherently with the original character
multiplicities; the fixed convention `sgn(0)=1` deliberately does not do
that.
