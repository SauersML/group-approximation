---
rg: 2
id: taller-vidick-positive-noise-fixed-support-reweighting
kind: claim
title: Taller--Vidick positive-noise tests have fixed support, but reweighting does not create perfect completeness
distinct_from:
  taller-vidick-lcs-re-hardness: that is the published RE-hardness theorem and its quantitative decoder; this fixes one `(u,B,pi)` and separates its epsilon-independent equation support from its epsilon-dependent sampling law.
  reverse-kleene-does-not-remove-tv-completeness-loss: that audits a recursion-theorem argument; this proves the exact finite reweighting and weighted proof-certificate estimates that such an argument may use.
  subgroup-dehn-function-is-the-hyperlinearity-modulus: that gives an unweighted asymptotic area modulus for subgroup words; this gives the sharp elementary weighted Cauchy--Schwarz bound for one fixed certificate.
---

**ESTABLISHED FIXED-SUPPORT AND REWEIGHTING AUDIT.**  Fix finite
`(u,B,pi)` in the Taller--Vidick test `L^epsilon(u,B,pi)`, with the paper's
nonempty-constraint hypothesis.  For all

```text
0<epsilon<1,                                             (TVF1)
```

the variables and three-variable parity equations underlying the test are
the same finite LCS.  Only their sampling probabilities depend on `epsilon`.
Indeed, for each fixed sampled `(W,U,C,f,g)`, every mask
`mu in F_W` has probability

```text
epsilon^(|mu^-1(-1)|) (1-epsilon)^(|mu^-1(1)|)>0,       (TVF2)
```

and `g'=fgmu` determines `mu`.  The right-hand side of the resulting parity
equation is determined by `(f,g,g')`, not by the numerical value of
`epsilon`.  At `epsilon=0` this support collapses to the constant-one mask,
so zero noise is still a different presentation.

More generally, let `R` be any finite test support and let `p,q` be two
full-support probability laws on it.  If `ell_r(sigma) in [0,1]` is the loss
of a strategy on test `r`, then, strategy by strategy,

```text
sum_r q_r ell_r >= kappa(q|p) sum_r p_r ell_r,
kappa(q|p)=min_r q_r/p_r,                               (TVF3)

sum_r q_r ell_r <= K(q|p) sum_r p_r ell_r,
K(q|p)=max_r q_r/p_r.                                   (TVF4)
```

Consequently `val_p<=s<1` implies

```text
val_q<=1-kappa(q|p)(1-s)<1.                             (TVF5)
```

Strict soundness is invariant under full-support reweighting.  Near-perfect
completeness is not: a `p`-loss at most `eta` gives only `q`-loss at most
`K(q|p)eta`.  For a fixed full-support `q`, rare Taller--Vidick mask cells
have `p_epsilon`-weight of order `epsilon^M`, where
`M=|{+1,-1}^W|`; hence `K(q|p_epsilon)` can grow as
`epsilon^-M`.  The published `eta=epsilon` bound therefore gives no
vanishing loss under a fixed reweighting.

There is also an exact weighted van Kampen estimate.  Let
`Gamma=<S|R>` and suppose a word has a certificate

```text
u=product_j v_j r_j^(sigma_j) v_j^-1,
m_r=#{j:r_j=r},
A_p(D)=sum_(r in R) m_r^2/p_r.                           (TVF6)
```

For every unitary tuple `U`,

```text
sum_r p_r ||r(U)-1||_2^2
 >= ||u(U)-1||_2^2/A_p(D).                              (TVF7)
```

In particular, on a sector where `u(U)=-1`,

```text
sum_r p_r ||r(U)-1||_2^2 >= 4/A_p(D).                   (TVF8)
```

This is a certificate-dependent proof gap, not a perfect-completeness
upgrade.  It applies only after a derivation of `u=1` is known, and its
denominator depends on both that derivation and the sampling weights.

Finally, the published main reduction does not fix `u` while taking
`epsilon` to zero.  In the proof of its main theorem, `u` is selected after
`epsilon` so that the repeated-game bound `s''(u)` satisfies

```text
s''(u)<4 epsilon delta^2.                               (TVF9)
```

For fixed `u`, the positive-noise presentation is indeed fixed, but `(TVF9)`
eventually fails as `epsilon` decreases.  Thus fixed support, full-support
reweighting, and `(TVF8)` do not supply a single LCS with both exact
completeness and the published constant soundness.  No proof-gap crossing or
nonhyperlinear group follows from these observations alone.

