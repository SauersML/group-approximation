---
rg: 2
id: fournier-facio-dimension-face-calibration-proof
kind: route
title: Rotate each approximation block by a concentrated Haar unitary and take an ultralimit of uniform block charges
target: fournier-facio-dimension-face-holds-every-approximation
requires:
  - fournier-facio-generator-support-components-escape-cutoffs
---

**Normalization.**  Replacing `phi_n` by `phi_n tensor 1_(m_n)` preserves both
normalized-HS limits, so assume `d_n -> infinity`.  Fix finite sets
`B_1<=B_2<=...` exhausting `G`, chosen so that `|B_n|^2<=d_n`, and put
`eps_n=d_n^(-1/3)`.

**Concentration.**  Let `v` be a Haar-random unit vector in `C^d` and `T` a
matrix with `||T||_op<=4`.  The map `v |-> <v,Tv>` is `8`-Lipschitz on the
sphere, and its mean is `tr(T)`.  Levy concentration gives absolute constants
`c,c'>0` with

```text
P(|<v,Tv>-tr(T)|>eps) <= c exp(-c' d eps^2).                 (DFP1)
```

Each column `W delta_x` of a Haar unitary `W in U(d_n)` is a Haar unit
vector.  Apply `(DFP1)` to the at most `2|B_n|^2` operators

```text
T=phi_n(g)            (g in B_n),
T=D^* D,  D=phi_n(gh)-phi_n(g)phi_n(h)     (g,h in B_n),
```

and to the `d_n` columns.  A union bound gives failure probability at most
`2 c d_n^2 exp(-c' d_n^(1/3))`, which is less than one for large `n`.  Fix such
a `W_n` for every large `n`, and any `W_n` for the finitely many remaining
`n`; finitely many blocks have charge zero below, so they play no role.  Then for every `x in [d_n]`:

```text
|<W_n delta_x, phi_n(g) W_n delta_x> - tr(phi_n(g))| <= eps_n,
| ||D W_n delta_x||^2 - ||D||_2^2 | <= eps_n.                 (DFP2)
```

**The charge.**  Let `omega` be a free ultrafilter on `N` and define
`mu(A)=lim_omega |A cap [d_n]|/d_n` on subsets of `X`.  It is a finitely
additive probability charge.  A finite set meets finitely many blocks with
weights at most `(size)/d_n -> 0`, so `mu` vanishes on finite sets and the
charged diagonal state kills compact operators.

**Invariance.**  `pi(g)` is block diagonal, so the block-`n` diagonal average
of `pi(g)^* T pi(g)` depends only on the block `T_nn` and equals
`tr(psi_n(g)^* T_nn psi_n(g))=tr(T_nn)`, with
`psi_n(g)=W_n^* phi_n(g) W_n`.  Taking `lim_omega` gives invariance of the
charged state under every `Ad(pi(g))`.

**Near multiplicativity and essential freeness.**  Fix `g,h` and `eps>0`.  For
all large `n`, `g,h in B_n` and `||D||_2^2+eps_n<eps^2`, so by `(DFP2)` no basis
vector of block `n` has `||(pi(gh)-pi(g)pi(h))delta_x||>=eps`.  The
exceptional set lies in finitely many blocks and is `mu`-null.  Likewise, for
`g!=1`, `|<delta_x,pi(g)delta_x>|<=|tr(phi_n(g))|+eps_n -> 0` uniformly on
large blocks.

**Faces.**  Every actor preserves every block `[d_n]`, so every support
component is finite (it lies inside a block), and the block near action is
trivial.  `fournier-facio-generator-support-components-escape-cutoffs`, applied
to this witness with the actors as comparison unitaries, gives charge zero to
every bounded component-size stratum.  So the witness lies on face (S2): all
charge on finite components with sizes escaping every cutoff.
