---
rg: 2
id: explicit-commuting-operator-separating-game
kind: claim
title: An explicit finite game has commuting-operator value one and entangled value at most one half
artifacts:
  - research/artifacts/mipstar-re-ingestion-2026-08-20.md
distinct_from:
  mipstar-equals-re: that is the complexity characterization and gives a family of games indexed by Turing machines, with no single member known to separate the two values; this is one explicit game for which the separation is proved.
  perfect-zpc-irs-quantum-gap-game: that separates the ZPC-IRS value from the finite-dimensional quantum value for a tailored game; this separates the commuting-operator value from the entangled value for a plain nonlocal game.
  phase-safe-toric-gap-game-exists: that asks for a phase-safe toric-style game whose perfect model compiles to a group; this asserts no group-theoretic property and is already proved.
---

**Established by citation.**  Ji, Natarajan, Vidick, Wright and Yuen,
arXiv:2001.04383, Theorem 12.13.  There is an explicitly constructed finite
two-player one-round game `G^sep` with

```text
val*(G^sep) <= 1/2      and      val^co(G^sep) = 1,
```

where `val^co` is the supremum over commuting-operator strategies.  In
particular `G^sep` witnesses `C_qa != C_qc` concretely, rather than through the
non-constructive route of undecidability.

**How it is built, and the peculiarity worth recording.**  `G^sep` is the fixed
point of a verifier that runs the Navascues--Pironio--Acin semidefinite
programming hierarchy on the game *it is itself defining*, and halts if the
hierarchy ever certifies a commuting-operator value below one.  If the
commuting-operator value were below one the hierarchy would eventually detect
it, the verifier would halt, and the entangled value would be one -- a
contradiction.  So the commuting-operator value is one, and the compression
theorem then forces unbounded entanglement and hence `val* <= 1/2`.

**The proof does not exhibit a value-one commuting-operator strategy.**  This is
explicit in the source: the argument establishes `val^co(G^sep)=1` by
contradiction, without producing the strategy.  The authors separately conjecture
that `val^co(G_M) = 1` for *every* non-halting `M`, and note it appears
difficult to identify an explicit witnessing strategy in any single instance.
For this program that matters: a construction that needs a concrete
commuting-operator strategy to groupify cannot take one from here.

The source estimates the size of the resulting separating correlation is not
astronomical, offering `10^20` as a believed but unproved upper bound on the
number of questions and answers.
