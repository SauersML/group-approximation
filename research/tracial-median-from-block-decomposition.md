---
rg: 2
id: tracial-median-from-block-decomposition
kind: route
title: Pin the size observable by spectral coarea against uniform block expansion
target: tracial-median-concentration
requires: [hs-expander-block-decomposition]
artifacts:
  - docs/TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md
  - official/counterexample.tex
---

Assume the nested pair of block algebras, with uniform gap constant
`kappa'` on each block.  Build `M` and `f` as in the target claim; `f` is a
positive contraction lying in the same abelian algebra, so its spectral
projections `P_t = 1_[t,infinity)(f)` lie there too and commute with every
`q_A`.

**One-sided drift.**  For `s` a `Gamma`-generator, `f` is almost invariant
because `M` is.  For a compressor `t_i`, the compression `t_i Gamma t_i^(-1)
<= Gamma` makes `phi(t_i) p_j phi(t_i)^*` almost supported in a single fine
block whose trace is at least `tau(p_j)` up to the decomposition error, so
`M` almost increases along `t_i`; the manuscript's elementary inequality
`(1-eta)x/((1-eta)x+a) >= x/(x+a) - eta` (`official/counterexample.tex:322`)
transfers verbatim by functional calculus, since both sides are increasing
scalar functions applied to commuting positive operators.  This yields
`phi(s) f phi(s)^* >= f - eta` modulo a corner of small trace, for every
positive `G`-generator `s`.

**Conservation.**  `tau(u f u^* - f) = 0` for `u` unitary, so by the lemma
in `hs-block-decomposition-to-steinberg-stable` the one-sided bound upgrades
to `‖phi(s) f phi(s)^* - f‖_1 = o(1)`, summed over `S_G`.

**Coarea.**  Apply `(SCI2)` of `docs/TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md`
with `H = f` and the arrows `A = phi(s)`, `s in S_G`.  The integral over
thresholds of the commutator energy of the spectral cuts is bounded by the
commutator energy of `f` itself, which the previous step made `o(1)`.

**Cheeger.**  This step is a computation, not a hypothesis.  The gap in the
form demanded by `hs-expander-block-decomposition` yields a tracial Cheeger
inequality for every cut inside a block.

> **Lemma (tracial Cheeger from a block gap).**  Let `q` be a projection in
> a finite von Neumann algebra `(M,tau)`, let `tau_q = tau(.)/tau(q)`, let
> `u_s in U(qMq)` for `s` in a finite set `S`, and suppose
> `sum_s ‖u_s x - x u_s‖_(2,q)^2 >= kappa'^2 ‖x - tau_q(x)q‖_(2,q)^2` for
> every `x=x^*` in `qMq`.  Then for every projection `P <= q`,
>
> ```text
> sum_(s in S) ‖(q-P) u_s P‖_(2,q)^2
>   >= (kappa'^2/2) tau_q(P) tau_q(q-P)
>   >= (kappa'^2/4) min(tau_q(P), tau_q(q-P)).
> ```

*Proof.*  Put `A_s=(q-P)u_sP` and `B_s=Pu_s(q-P)`, so `[u_s,P]=A_s-B_s`.
They are orthogonal, since `tau(B_s^*A_s)=tau((q-P)u_s^*P(q-P)u_sP)=0`, and
they have equal norm: `tau(A_s^*A_s)=tau(u_sPu_s^*)-tau(Pu_sPu_s^*)` and
`tau(B_s^*B_s)=tau(P)-tau(Pu_sPu_s^*)`, and `tau(u_sPu_s^*)=tau(P)`.  Hence
`sum_s ‖[u_s,P]‖^2 = 2 sum_s ‖A_s‖^2`.  Apply the gap to `x=P`, using
`‖P-tau_q(P)q‖_(2,q)^2 = tau_q(P)-tau_q(P)^2`.  The last inequality holds
because the larger of `tau_q(P)` and `tau_q(q-P)` is at least `1/2`.  QED

So the gap hypothesis IS the Cheeger inequality, with `gamma = kappa'^2/4`,
and no separate expansion input is required.  Median normalization supplies
the side condition the manuscript needs: because `1/2` is a fiberwise median
of `f`, for `t<1/2` the sublevel set is the smaller side inside `q_A` and
for `t>1/2` the superlevel set is, so the `min` above is the side being
bounded.  Splitting the threshold integral at `1/2` gives
`kappa'^2 * ‖f - 1/2‖_1 = o(1)` up to absolute constants.

Inverting `M = m_A f (1-f)^(-1)` on the corner where `|f - 1/2| <= delta`
then gives the trace-ratio bound with `rho -> 1`, which is the target.

**Status.**  The drift clause used in the first step is now part of the
statement of `hs-expander-block-decomposition` rather than a caveat carried
here.  That change was made because a route asserts its implication, and
this route previously flagged a hole in prose while presenting itself as a
derivation -- the same failure the graph records as restatement dressed as
reduction, in its other common form.  With the drift clause in the
prerequisite and the Cheeger lemma proved above, the chain from the
prerequisite to the target is complete except for the error bookkeeping
noted at the end.

Two things this route does **not** need, contrary to how the step was first
scoped.  It needs no separate expansion or Cheeger hypothesis beyond the
block gap, by the lemma.  And it needs no boundedness argument for the size
observable: the manuscript renormalizes because "the values of `M` need not
be uniformly bounded" (`official/counterexample.tex:310`), whereas tracially
`M = sum_i tau(p_i) p_i <= 1` by construction, so `M(M+m_A)^(-1)` is
continuous functional calculus of a positive contraction.  The median
normalization survives for a different reason -- it is what places the
median at `1/2` fiberwise, which is what makes the `min` in the lemma land
on the side being estimated.

One caveat on the lemma's hypotheses in the intended application.  It is
stated for genuine unitaries `u_s in U(qMq)`, while the compressions
`q phi(s) q` of an almost-representation are only almost unitary in `qMq`.
The defect is controlled by `‖[phi(s),q]‖_2`, which the decomposition makes
small, but the resulting error term has not been tracked here.
