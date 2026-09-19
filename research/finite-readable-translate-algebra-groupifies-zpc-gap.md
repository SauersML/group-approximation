---
rg: 2
id: finite-readable-translate-algebra-groupifies-zpc-gap
kind: claim
title: A finite readable translate algebra groupifies a perfect ZPC quantum gap
distinct_from:
  finite-invariant-partition-only-reduces-irs-to-fiber-irs: that transfers only the stabilizer character to one finite-index fiber and therefore still needs a regular fiber; this uses every controlled verifier row and the strict quantum gap to prove a quotient of the fiber stabilizer nonhyperlinear without regularizing its character.
  zpc-readable-control-freezing-to-lcs: that asks for one fixed readable assignment supporting an ordinary LCS solution; this permits the readable assignment and equation menu to move around a finite orbit and produces a finite-index stabilizer quotient instead of an LCS solution group.
  zpc-frozen-equation-menu-has-positive-orbitwise-class: that asks one menu to remain valid on every unreadable translate; this kills the different active menu at each orbit atom after conjugating it back to one stabilizer.
  finite-depth-readable-groupoid-closes-iff-full-orbit-is-finite: that characterizes the finite-translate hypothesis and its failure; this proves that the hypothesis is terminal for a perfect game with a strict quantum gap.
---

Let `G` be a finite controlled-linear tailored game with a perfect ZPC-IRS
strategy and

```text
omega*(G)<1.                                             (FRT1)
```

Let `phi(g)=mu(Fix(g))` be the stabilizer character of the underlying p.m.p.
action and let `(M,tau,pi)` be its faithful tracial GNS von Neumann algebra.
This is the fixed-point-character GNS represented inside the orbit-relation
algebra, not the ordinary action crossed product with its regular Fourier
trace.  Put

```text
q_-=(1-pi(J))/2.
```

The freeness of `J` gives `tau(q_-)=1/2`; equip the negative corner with its
normalized faithful trace

```text
tau_-(x)=2 tau(x)=tau((1-pi(J))x),       x in q_- M q_-.
```

Let `Q_G` be the finitely presented structural group on `J` and all
unreadable involutions, with `J` central and with every
unreadable--unreadable commutator required either at one question or across
an edge in the support of the game distribution.  The unreadable part of
`pi` factors through `Q_G`.

Inside `q_- M q_-`, let `D_0` be the joint spectral algebra of all readable
involutions and set

```text
D_infinity = W*( pi(g) D_0 pi(g)^* : g in Q_G ).         (FRT2)
```

This algebra is abelian.  Indeed, put `A_r={x:r x=x}`.  Z alignment and
freeness of `J` make `A_r` a `J`-invariant measurable set and write the
readable involution `r` in the relation algebra as

```text
pi(r)=1_(A_r)+1_(A_r^c) pi(J)
```

for a `J`-invariant measurable set `A_r`.  Hence

```text
q_- (1+pi(r))/2 = q_- 1_(A_r),
pi(g) q_- 1_A pi(g)^* = q_- 1_(gA).
```

Every group generator commutes with `J`, so `gA` is again `J`-invariant.
Thus all translates of `D_0` lie in the abelian algebra

```text
{ q_- M_f : f in L^infinity(X)^J }
```

inside the relation-algebra representation.  Here `M_f` is multiplication by
`f`; the assertion does not call `q_-` itself Cartan-diagonal.

Assume that `D_infinity` is finite dimensional.  Let `T` be any orbit of
its atoms under `Q_G`, choose `t_0 in T`, and put

```text
H=Stab_(Q_G)(t_0).
```

Choose left-coset representatives `x_t H`, with `x_t t_0=t`.  Every atom
`p_t` lies below a unique joint readable profile `r(t)`.  For every affine
row active at that profile, write its unreadable word, after substituting the
readable signs, as

```text
c_(t,a)=w_(t,a) J^(b_(t,a)),
```

normalized so that acceptance is `c_(t,a)=1`.  Perfectness implies that
`c_(t,a)` fixes `p_t`; hence

```text
h_(t,a)=x_t^(-1) c_(t,a) x_t in H.
```

Define

```text
K_T = H / << h_(t,a) : t in T, a an active row at t >>_H. (FRT3)
```

Then `K_T` is finitely presented, the image of `J` in `K_T` is central and
nontrivial, and `K_T` is not hyperlinear.  Thus every atom orbit of a finite
full readable translate algebra supplies a finitely presented
nonhyperlinear group.  Neither an invariant readable atom, an orbitwise
constant equation menu, nor a regular fiber character is required.
