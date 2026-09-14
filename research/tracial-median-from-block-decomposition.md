---
rg: 2
id: tracial-median-from-block-decomposition
kind: route
title: Pin the size observable directly with the block Poincare gap
target: tracial-median-concentration
requires: [hs-expander-block-decomposition, median-poincare-concentration]
artifacts:
  - c1168433:official/counterexample.tex
---

Assume the nested pair of block algebras from
`hs-expander-block-decomposition`, with a uniform gap constant `kappa'` on
each coarse ambient block.  Build `M` and `f` as in the target claim.  Thus
`0 <= f <= p`, `f` commutes with every coarse block `q_A`, and `1/2` is a
median of the spectral distribution of `f_A = q_A f` for the normalized
trace on every nonzero `q_A`.

The old route converted the block Poincare inequality to a Cheeger inequality,
then used spectral coarea, and therefore inherited an irrelevant genuine-
unitary hypothesis in that conversion.  The claim
`median-poincare-concentration` shows that none of this is needed: apply the
Poincare inequality to `f` itself.

**One-sided drift.**  For a `Gamma` generator, `f` is almost invariant because
the fine block-size observable `M` is.  For a compressor `t_i`, the clause

```text
phi(t_i) p_j phi(t_i)^*  ~=  p_(sigma(j)),
tau(p_(sigma(j))) >= tau(p_j) - eps(delta)
```

makes `M` almost increase along `t_i`.  The scalar inequality used in the
manuscript,

```text
(1-eta)x / ((1-eta)x+a) >= x/(x+a) - eta,
```

passes through the commuting functional calculus defining `f`.  Hence, up to
the small discarded corner supplied by the decomposition,

```text
phi(s) f phi(s)^* >= f - o(1)
```

for every generator `s` used by the coarse block gap.

**Trace conservation turns the one-sided inequality into `L^2`
invariance.**  Since `phi(s)` is unitary in the ambient matrix algebra,
`tau(phi(s) f phi(s)^*) = tau(f)`.  The elementary positive/negative-part
argument already used in `hs-block-decomposition-to-steinberg-stable`
therefore gives

```text
||phi(s) f phi(s)^* - f||_1 = o(1).
```

Both terms are positive contractions, so their difference has operator norm
at most `1`.  Consequently

```text
||phi(s) f phi(s)^* - f||_2^2
 <= ||phi(s) f phi(s)^* - f||_1
 = o(1),
```

and, by unitary invariance,
`||[phi(s),f]||_2 = o(1)`.

**Apply the gap blockwise, without unitary compression bookkeeping.**  Put
`a_(A,s) = q_A phi(s) q_A`.  Because `q_A` commutes with `f`,

```text
[a_(A,s), f_A] = q_A [phi(s),f] q_A.
```

The coarse-block clause of `hs-expander-block-decomposition` assumes the
Poincare inequality for these very compressed operators.  It does not merely
assert that they are close to some genuine unitary.  Thus
`median-poincare-concentration` applies to each `q_A` even though
`a_(A,s)` is only an almost-unitary.  With `C=(1+sqrt(2))^2`, it gives

```text
tau(q_A) ||f_A-(1/2)q_A||_(2,A)^2
 <= (C/kappa'^2) sum_s ||q_A[phi(s),f]q_A||_2^2.
```

Sum over `A`.  Orthogonal block compression is contractive in `L^2`, so

```text
||p f-(1/2)p||_2^2
 <= (C/kappa'^2) sum_s ||[phi(s),f]||_2^2
 = o(1).
```

The discarded complement has `tau(1-p)=o(1)`, hence normalized
Cauchy--Schwarz yields the target conclusion

```text
||f-1/2||_1 = o(1).
```

Finally choose `delta_n -> 0` slowly enough that the spectral projection

```text
e_n = 1_[1/2-delta_n, 1/2+delta_n](f)
```

has trace tending to `1`.  On a fine block `p_i <= q_A`, `f` has the scalar
value

```text
tau(p_i)/(tau(p_i)+m_A).
```

Solving for `tau(p_i)` shows that two fine blocks meeting `e_n` in the same
`q_A` have trace ratio trapped between quantities tending to `1`.  This is
exactly the operative output of `tracial-median-concentration`.

**Which compressor clause the drift uses (2026-09-11).**  The one-sided drift
above needs the multiplicative estimate
`tau(p_(sigma(j))) >= (1 - eta) tau(p_j)` on most mass.  The per-atom
additive clause formerly written in `hs-expander-block-decomposition` does
not give it: it is automatic below trace `eps(delta)^2/4`
(`hs-per-atom-compressor-clause-is-vacuous`).  The prerequisite now states
the mass-weighted clause.  By that claim, off atoms of total trace
`8 eps + eps^(1/2)` the matching is injective and non-shrinking with
`eta = 2 eps^(1/4)`, which is what the functional-calculus inequality
consumes.

**Redundant for the Leavitt consumer.**  With scalar fine gaps, the fine
atom algebra is already a masa of the relative commutant of `Gamma`.  So
`transported-gap-masa-kills-leavitt-hs-models` reaches the stable branch
directly from the fine clauses and the `u`-clause, without this median step
(`hs-blocks-select-stable-branch-through-masa-transport`).  This route
remains valid; it is simply no longer on the shortest path.

**What disappeared.**  There is no coarea step, no Cheeger conversion, and no
need to prove that `q_A phi(s) q_A` is close enough to a genuine unitary for a
projection-boundary calculation.  The spectral-gap inequality demanded by
the prerequisite is already the stronger analytic object.  The previously
recorded almost-unitary bookkeeping debt was an artefact of taking an
unnecessary detour through cuts.