---
rg: 2
id: tracial-median-concentration
kind: claim
title: Tracial median concentration of the block-size observable
distinct_from:
  hs-expander-block-decomposition: That produces the blocks; this concentrates their traces once they exist, and is the step the permutation argument spends its median device on.
  leavitt-steinberg-hs-stable: That is the branch selection; this is one of the two inputs a transcription of the nonsoficity argument would need.
  invariant-size-collapse: That is the exact algebraic statement that a conjugation-invariant strictly monotone size makes a compression an equality; this is the quantitative approximate substitute, needed precisely because the trace is refinement-blind and supplies no such size.
artifacts:
  - c1168433:official/counterexample.tex
---

Given a nested pair of almost-invariant block algebras as in
`hs-expander-block-decomposition` -- coarse ambient blocks `q_A` almost
invariant under `G`, fine blocks `p_i` almost invariant under `Gamma`, all
inside one abelian algebra -- put

```text
M = sum_i tau(p_i) p_i,
f = sum_A q_A * M (M + m_A)^(-1) q_A,
```

where `m_A` is a median of the distribution of `M` in the corner `q_A`
normalized by `tau(q_A)`.  Ask for

```text
||f - 1/2||_1 -> 0,
```

hence a projection `e` of trace tending to `1` such that any two fine blocks
meeting `e` inside a common ambient block have traces differing by a factor
tending to `1`.

That last sentence is the operative output.  The unequal-trace case is not a
case to be handled separately: this claim is exactly the assertion that the
fine blocks become asymptotically equitracial inside each coarse block.

## Why the median normalization is the right statistic

In the finite permutation proof, `M(z)` is the size of the `Gamma` component
containing `z`; the median device turns a one-sided component-size drift into
a statement that component sizes in one ambient component are almost equal.
Tracially `M <= 1`, so raw boundedness is not the problem.  The reason to keep

```text
f = M/(M+m_A)
```

is **relative scale**: atom traces may vanish with the matrix dimension, and
additive concentration of `M` around a tiny mean would not imply that two
atom traces have ratio tending to `1`.  The transform places the fiberwise
median at the dimensionless value `1/2`; concentration there is exactly a
multiplicative trace-ratio statement after inversion.

There is a useful population-genetic reading.  If the fine atom traces are
`s_i=tau(p_i)`, then the spectral law of `M` under `tau` is the size-biased
frequency spectrum

```text
Pr[M=s_i] = s_i,
```

and

```text
tau(M^r) = sum_i s_i^(r+1).
```

Thus `tau(M)=sum_i s_i^2` is the collision/homozygosity statistic of the block
partition.  This dictionary is useful mainly because it says what **not** to
optimize: fixed diversity moments are refinement-blind in exactly the wrong
way.  For `d` rank-one blocks, `s_i=1/d`, every fixed positive moment tends to
zero while two distinct rank-one projections are only `sqrt(2/d)` apart in
normalized Hilbert--Schmidt norm.  Moment control alone therefore cannot
recover the injective block matching the hyperlinear attack needs.  The
fiberwise median/quantile keeps the relative information that those moments
lose.

## The concentration step is no longer a second obstruction

The original transcription followed the finite proof literally: spectral
coarea, then a Cheeger inequality for threshold projections.  That route was
correct for genuine block unitaries but created an avoidable bookkeeping debt
because `q_A phi(s) q_A` is only an almost-unitary.

`median-poincare-concentration` removes the detour.  The block decomposition
already asks for the stronger Poincare inequality

```text
sum_s ||a_s x-x a_s||_(2,A)^2
 >= kappa'^2 ||x-tau_A(x)q_A||_(2,A)^2
```

for the compressed operators `a_s=q_A phi(s) q_A` themselves.  Once the
one-sided compressor drift and trace conservation make `f` almost invariant,
apply that inequality directly to `x=f`.  The median pins the scalar supplied
by the Poincare estimate to `1/2`.  No unitarity of the compressed operators,
no threshold cuts, and no Cheeger conversion are needed.

So the load-bearing unknown remains exactly
`hs-expander-block-decomposition`: produce the nested blocks, their uniform
gap, and the one-block compressor drift.  Once that exists, the median step
is an analytic consequence rather than an additional frontier hole.