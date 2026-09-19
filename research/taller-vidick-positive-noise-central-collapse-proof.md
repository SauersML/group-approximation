---
rg: 2
id: taller-vidick-positive-noise-central-collapse-proof
kind: route
title: Extract the two-mask certificate that kills the Taller--Vidick sign
target: taller-vidick-positive-noise-collapses-central-sign
requires:
  - taller-vidick-positive-noise-fixed-support-reweighting
---

We use the notation of Taller--Vidick Definition 4.1. For a sign
`a in {+1,-1}`, write

```text
[a]=1 if a=+1,       [a]=J if a=-1.                    (TVP1)
```

Thus `[ab]=[a][b]`. Let `x_(U,s_U(f))` and
`x_(W,s_(g,C))` denote the solution-group generators attached to the
corresponding LCS variables. The equation produced by a tuple
`(W,U,C,f,g,g')` is

```text
x_(U,s_U(f)) x_(W,s_(g,C)) x_(W,s_(g',C))
  = [m_f m_(g,C) m_(g',C)].                            (TVP2)
```

Repeated variables in `(TVP2)` are read with their parity multiplicity,
equivalently they cancel using the defining involution relations.

Fix one supported outer tuple `(W,U,C)` and arbitrary functions
`f in F_U`, `g in F_W`. Regard `f` as the function
`y -> f(y|_U)` on the assignment cube of `W`. Since
`0<epsilon<1`, every mask in `F_W` occurs with positive probability.
In particular

```text
mu_+=f                                                     (TVP3)
```

occurs. It gives `g'=f g mu_+=g`. Substitution in `(TVP2)` yields

```text
x_(U,s_U(f)) x_(W,s_(g,C))^2
  = [m_f m_(g,C)^2]=[m_f].                              (TVP4)
```

Every solution-group variable is an involution, so

```text
x_(U,s_U(f))=[m_f].                                    (TVP5)
```

Now use the query `-f` and the also-supported mask

```text
mu_-=-f.                                                (TVP6)
```

Again `g'=(-f)g(-f)=g`. Folding over true has the exact identities

```text
s_U(-f)=s_U(f),       m_(-f)=-m_f.                      (TVP7)
```

Indeed `s_U` chooses the same representative from `{f,-f}`, and
multiplying that representative by `-f` reverses the constant sign used
to define `m_f`. Therefore the second instance of `(TVP2)` has the
same left-hand side as `(TVP4)` but gives

```text
x_(U,s_U(f))=[-m_f]=J[m_f].                             (TVP8)
```

Comparing `(TVP5)` and `(TVP8)`, then multiplying by the involution
`[m_f]`, proves `J=1`.

This is a presentation-theoretic statement, not merely a value estimate.
By the standard solution-group criterion, a perfect commuting LCS strategy
would give a representation with `J=-1`, impossible when `J=1`.
The certificate uses no property of `B`, its perfect strategy, the
repetition count, or the numerical noise weight beyond full mask support.

At zero noise only `mu=1` occurs. Unless the chosen lifted `f` happens
to be constant, neither `(TVP3)` nor `(TVP6)` is then simultaneously
present. This pinpoints why deleting the noisy masks changes the algebra
rather than continuously improving completeness.

For the direct gap, let `q_+` and `q_-` denote the probabilities of the
two full tuples used above. In each tuple the last two LCS occurrences are
the same variable, so their two equal assignment bits cancel. Alice's first
bit is therefore forced to `m_f` in the first context and to `-m_f` in
the second. Condition on Bob receiving the common first query, an event of
probability `1/3` in each tuple. If `r` is Bob's probability of returning
`m_f` on that query, the loss contributed by these two contexts is

```text
(q_+/3)(1-r)+(q_-/3)r >= min(q_+,q_-)/3.                (TVP9)
```

This uses no finite-dimensional or synchrony assumption and proves
`(TVC4)`.

Now replace full Bernoulli support by a fixed support
`M subseteq F_W`, sampled independently of the query function `f`.
The proof `(TVP3)--(TVP8)` is available precisely when `M` contains both
members of a lifted antipodal pair `{f^up,-f^up}`; this proves `(TVC5)`
for this two-equation certificate.

Let `S` be the honest assignment support. On a dictator at
`phi in S`, the three honest answers in the test equation multiply to
`mu(phi)`. Exact acceptance for every positive honest atom is therefore
equivalent to `mu(phi)=1` for every `phi in S` and every supported mask,
which is `(TVC6)`. If `S` is nonempty, `mu` and `-mu` cannot both
belong to `A_S`. If the full assignment cube has a point outside `S`,
flipping the mask only at that point gives a nonconstant member of `A_S`,
so a support strictly larger than `{1}` exists.

Finally, for `beta subseteq S` and every `mu in A_S`,

```text
chi_beta(mu)=product_(phi in beta) mu(phi)=1.            (TVP10)
```

Averaging proves `(TVC7)`. Folding removes even Fourier degrees, so any
three-element subset of `S` is an undamped odd non-dictator character.
This proves the stated `|S|<=2` necessary condition and completes the
support-design audit.

