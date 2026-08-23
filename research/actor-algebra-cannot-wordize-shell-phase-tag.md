---
rg: 2
id: actor-algebra-cannot-wordize-shell-phase-tag
kind: claim
title: The native actor group algebra cannot wordize an injective shell phase tag
distinct_from:
  fixed-spherical-polynomials-have-no-42nd-projection: that uses connected spherical spectrum to rule out one trace-1/42 projection from fixed Hecke polynomials; this gives a finite 42-point obstruction to the entire injective diagonal tag inside the actor group algebra.
  native-forty-two-shell-has-a-noncommuting-pair: that rules out the Boolean Fourier construction from native lamp conjugates; this rules out the alternative construction using only actor, root, Weyl, and parahoric section words.
  one-phase-chart-tag-pays-atomwise-leakage: that proves an abstract injective tag would control EDA11; this proves such a tag is separated by a fixed HS gap from every actor group-algebra expression on the native shell.
---

Let a group `G` act transitively on a finite set `Omega` of size `q>=2`, and
let `rho` be its permutation representation on `l^2(Omega)`. Write `P_i`
for the coordinate projections and choose all `q` distinct `q`-th roots of
unity `zeta^i`. The injective coordinate phase tag is

```text
A=sum_(i=0)^(q-1) zeta^i P_i.                          (AAW1)
```

Then for every element `X` of the finite-dimensional actor algebra

```text
Alg_G=span{rho(g):g in G},                             (AAW2)
```

one has

```text
||A-X||_2^2>=2/q.                                      (AAW3)
```

The same estimate holds after arbitrary multiplicity amplification, with
`A` replaced by `A tensor I_K` and `X` allowed to range over every operator
commuting with the amplified constant-line projection `J tensor I_K`.

In particular, on the native parahoric shell

```text
Omega=SL_3(Z)/D,                 q=42,                 (AAW4)
```

the distance from the desired chart tag to every fixed linear combination
of lattice actor words is at least

```text
sqrt(2/42)=sqrt(1/21).                                 (AAW5)
```

This includes every expression using only integral root words, Weyl words,
and the lattice section corrections `d_i`, because all of them lie in the
same actor group algebra, even with an arbitrary spectator multiplicity.
Increasing the polynomial degree or changing its coefficients cannot evade
`(AAW3)`.

Therefore the sufficient mixed row from
`one-phase-chart-tag-pays-atomwise-leakage` cannot be obtained as a fixed
actor group-algebra Fourier word. A viable wordization must use an algebra
outside the actor image: native lamp/selector variables, a nontrivial
crossed-product coefficient, or a nonlinear conductor-dependent spectral
cut. The first option is not supplied by the raw shell lamps, whose missing
nonedge commutators are exact in
`native-forty-two-shell-has-a-noncommuting-pair`; the last option needs a
new uniform word-complexity estimate.

Scope: denominator words do not preserve one fixed shell, so `(AAW3)` is not
a no-go for an enlarged-window construction using genuinely off-shell
coefficients. It rules out precisely the proposed fixed 42-point
actor/root/section group-algebra tag.
