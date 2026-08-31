# Ingestion audit: MIP* = RE

Date: 2026-08-20

Source handed over: the full LaTeX of Ji, Natarajan, Vidick, Wright, Yuen,
`MIP* = RE` (arXiv:2001.04383).  Read at source.

## 1. What the graph already had, and the defect

`MIP*=RE` is cited by eight nodes -- `mipstar-bcs-tracial-nonru-exists`,
`perfect-zpc-irs-quantum-gap-game`, `zpc-irs-value-computable-upper-hierarchy`,
`explicit-exact-support-lcs-witness`, `nonhyperlinear-from-exact-support-lcs`,
`hyperlinear-trace-not-mf-trace`, `consistency-defect-is-state-dependent-distance`,
and (as of this wave) `non-ce-bcs-has-finite-dimensional-forbidden-mass-gap`.

**It had no node of its own.**  Every one of those nodes opens with "by
`MIP*=RE`" and consumes a theorem the graph never stated.  This is the same
defect class found the previous day with Dogon--Vigdorovich, whose numbered
theorems were likewise cited everywhere and stated nowhere: a paper can be
load-bearing throughout a graph while remaining formally absent from it.
Neither Tsirelson's problem nor the refutation of Connes' Embedding Conjecture
was a node either.

Added: `mipstar-equals-re` (their Thm 12.9 and Cor 12.10) and
`explicit-commuting-operator-separating-game` (their Thm 12.13).

## 2. Two things worth carrying forward

**The authors state this program's goal as their own open question.**  Their
Section 1.3: one may ask whether the counterexample "can eventually lead to a
construction of a group that is not sofic, or even not hyperlinear".  So the
gap between "non-Connes-embeddable tracial von Neumann algebra" and
"non-hyperlinear group" is not an artifact of how this repository has framed the
problem; it is the gap the source itself flags.  Recorded on `mipstar-equals-re`.

**The explicit separating game comes with no explicit strategy.**  Theorem 12.13
gives a concrete finite game `G^sep` with `val^co = 1` and `val* <= 1/2`, but
the proof of `val^co(G^sep) = 1` is by contradiction against the NPA hierarchy
halting, and produces no commuting-operator strategy.  The authors separately
conjecture `val^co(G_M)=1` for every non-halting `M` and note the difficulty of
exhibiting a witness.  **Consequence for this program:** any groupification route
that needs a concrete value-one commuting-operator strategy as input cannot
source one here.  Recorded on
`explicit-commuting-operator-separating-game`.

## 3. Deliberately not authored

- No node for the compression theorem (their Thm 11.1), introspection, answer
  reduction, oracularization or anchored parallel repetition.  These are the
  internal machinery of the proof; nothing in this graph consumes them as
  hypotheses, and the ZPC lane's compiler targets
  (`zpc-selector-robust-lcs-compiler`,
  `zpc-robust-compiler-from-context-transducer`) are already stated in the
  weighted-algebra formalism they need.
- No node for Tsirelson's problem or the Connes Embedding Conjecture as separate
  statements.  Both are recorded inside `mipstar-equals-re` as consequences,
  with the Fritz / Junge et al. / Ozawa attributions the source gives; those
  papers were not read at source here.
- No node for the entanglement test of their Section 1.2 (question and answer
  length polynomial in the Kolmogorov complexity of `n`, forcing Schmidt rank
  `2^(Omega(n))`).  Nothing in the graph currently needs an entanglement lower
  bound of that shape.
