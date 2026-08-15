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
  - official/counterexample.tex
  - docs/TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md
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
normalized by `tau(q_A)`.  Ask for: `‖f - 1/2‖_1 -> 0`, hence a projection
`e` of trace `-> 1` such that any two fine blocks meeting `e` inside a common
ambient block have traces differing by a factor tending to `1`.

That last sentence is the operative output.  It says the fine blocks are
**asymptotically of equal trace**, which is why this node exists: the
unequal-trace case of the transcription is not a case to be handled
separately, it is this statement.

## Why this is the right unit

Reading `official/counterexample.tex:310-371` settles what the median device
is for.  It is not a technique for coping with unequal component sizes; it
is the proof that they are asymptotically equal.  The manuscript's `M(z)` is
the size of the `Gamma`-component of `z`, and the paragraph at `:310` says
plainly why raw sizes cannot be used -- "The values of `M` need not be
uniformly bounded, so these exceptional sets cannot control its total
variation" -- so `M` is renormalized to `f=M/(M+m_A)`, for which `1/2` is a
median on every ambient component `A`.  Its conclusion `(8)` at `:365-370` is

```text
rho_n^(-1) <= M(w)/M(z) <= rho_n,     rho_n -> 1,
```

for `z,w` in the same `A` off a set of size `o(N)`, glossed at `:371` as
"the sizes of original components meeting the same set `A \ E_n` differ by a
factor tending uniformly to one".  Step 3 then consumes exactly that: `(8)`
gives `|P triangle Q(P)| = o(|P|)`, hence `|P cap Q(P)| > |Q(P)|/2`, hence an
injective matching.

Tracially the boundedness worry is void -- `M <= 1` by construction, since
`tau(p_i) <= 1` -- so the normalization is a continuous functional calculus
of a bounded positive operator.  What survives as real content is the
concentration, and the demand that `m_A` be a **fiberwise** median over the
ambient blocks, which is why the pair must be nested.

## The obstruction is inherited, not new

The manuscript proves concentration by coarea plus Cheeger
(`:342-355`): the identity
`integral_0^1 |bd_A{f>t}| dt = sum_{edges in A} |f(z)-f(w)|`, then expansion
applied to sublevel and superlevel sets -- each of which has at most
`|A|/2` vertices on the relevant side precisely because `1/2` is a median of
`f` on `A` -- giving
`gamma_G sum_{z in A} |f(z)-1/2| <= sum_{edges} |f(z)-f(w)|`.

The two halves have very different status in the normalized-HS metric.

- **Coarea transcribes, and is already proved.**
  `docs/TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md` `(SCI2)`:
  `integral_0^1 ‖[P_t,A]‖_2^2 dt <= ‖[H,A]‖_2 ‖A‖_2` for the spectral
  projections `P_t` of a positive contraction `H`, with a common-threshold
  form `(SCI5)` for finitely many arrows.  This is the exact analogue of the
  finite coarea identity the manuscript uses.
- **Cheeger expansion does not, and is the same missing input.**  The
  inequality `|bd_A U| >= gamma_G min(|U|,|A \ U|)` is uniform expansion of
  the ambient blocks, which is Kun's theorem and hence
  `hs-expander-block-decomposition` again.

So this node does not add a second independent obstruction.  It shows the
one missing input is consumed **twice** -- once to produce the blocks, once
to pin the size observable -- and that the other half of the pinning step is
already available.  A proof that produced blocks without uniform gap would
still stall here.
