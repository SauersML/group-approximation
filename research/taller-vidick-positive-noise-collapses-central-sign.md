---
rg: 2
id: taller-vidick-positive-noise-collapses-central-sign
kind: claim
title: Every positive-noise Taller--Vidick LCS has trivial central sign
artifacts:
  - research/taller-vidick-positive-noise-central-collapse-proof.md
distinct_from:
  taller-vidick-positive-noise-fixed-support-reweighting: that proves the equation support is independent of the positive noise weight; this identifies a two-equation certificate inside that common support which forces the solution-group sign to be trivial.
  reverse-kleene-does-not-remove-tv-completeness-loss: that isolates an unknown certificate-dependent crossing gap; here the certificate that J equals one is explicit and exists for every positive-noise output, independently of the source instance.
  perfect-completeness-constant-soundness-lcs-compiler: that asks for a different exact compiler; this proves that neither reweighting nor flagging strategies can make the published positive-noise LCS presentation perfectly complete.
---

Fix finite `(u,B,pi)` satisfying the nonempty-constraint hypothesis in
Definition 4.1 of Taller--Vidick, arXiv:2507.22444v2, and let

```text
0<epsilon<1.
```

Let `Gamma_epsilon` be the solution group of the finite LCS underlying
`L^epsilon(u,B,pi)`, with distinguished central involution `J`. Then

```text
J=1 in Gamma_epsilon.                                  (TVC1)
```

In fact, `J` has a certificate using two test equations (besides the
standard involution relations). Fix any supported `(W,U,C)`, any
`f in F_U`, and any `g in F_W`. Lift `f` to `W` by restriction to
`U`. The two masks

```text
mu_+(y)= f(y|_U),       mu_-(y)= -f(y|_U)               (TVC2)
```

both have positive probability. For the first use the query `f`, and for
the second use `-f`. In both cases `g'=fgmu=g`, while folding identifies
the first LCS variable because

```text
s_U(-f)=s_U(f),         m_(-f)=-m_f.                    (TVC3)
```

Thus the two equations have literally the same left-hand side and opposite
right-hand sides. Their quotient is `J`, proving `(TVC1)`.

There is also a direct value gap. Let `q_+` and `q_-` be the sampling
probabilities of these two full equation contexts. In either equation the
last two occurrences are the same variable, so the parity relation fixes
the first answer deterministically to `m_f` or `-m_f`. Bob receives that
shared first-variable query with probability `1/3`. No response
distribution for Bob can agree with both opposite deterministic answers.
Thus, for arbitrary finite-dimensional or commuting strategies,

```text
omega(L^epsilon(u,B,pi))
  <= 1 - min(q_+,q_-)/3 < 1.                            (TVC4)
```

Consequently no positive-noise output of the published test has a perfect
commuting or finite-dimensional strategy, regardless of whether the source
BCS has a perfect strategy. Changing the positive mask weights, taking
one-sided limits of strategies, or attaching a strategy-level accept flag
without changing the equation support cannot create perfect completeness:
the same finite presentation still contains the certificate `J=1`.

This does not obstruct a genuinely different zero-noise presentation. At
`epsilon=0` only the constant-one mask is supported, so the two masks in
`(TVC2)` are not both available in general. The exact remaining seam is
therefore presentation-level: replace the full-support noisy test by new
finite equations whose perfect models survive while retaining a
dimension-independent decoder.
