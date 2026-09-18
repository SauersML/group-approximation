# Kari–Ollinger 2008: source record for the Kourovka 21.74 reduction

Lane bh-free-58. This file records what was read at source, for use by
`ct-z-finite-cycle-problems-are-undecidable`.

## Source

J. Kari and N. Ollinger, "Periodicity and Immortality in Reversible Computing",
MFCS 2008, LNCS 5162, Springer, pp. 419–430, doi 10.1007/978-3-540-85238-4_34
(HAL hal-00270815). The Springer PDF was fetched through MSI institutional access and is
stored in the swarm scratchpad as `gq/src/bh-free-58/kari-ollinger-mfcs2008.pdf`
(395860 bytes, md5 6d5a3e72ad3bb6dfd7b09d51125cbff6). Pages 419–424 and 430 were read.

## Definitions (Section 1.1, pp. 421–422), paraphrased

- A k-counter machine is `M = (S, k, T)`, with `S` a finite set of states and
  `T ⊆ S × {0,+}^k × Z_k × {−,0,+} × S`.
- An instruction `(s, u, i, φ, t)` applies to a configuration `(s, v) ∈ S × N^k` when the
  zero/positive pattern of `v` equals `u`. It moves to `(t, v')`, where `v'` is `v` with
  counter `i` decreased, unchanged or increased by one according to `φ`. A decrement is
  never allowed when `u(i) = 0`.
- `M` is deterministic (k-DCM) if at most one instruction applies to each configuration,
  i.e. the state and the test vector determine the action and the next state. Its
  transition function `G` is the resulting partial map on `S × N^k`.
- The reverse machine `M^{-1}` has the syntactically reversed instructions. `M` is
  reversible (k-RCM) when `M^{-1}` is deterministic as well.
- Section "Introduction" (p. 420):
  - Configurations on which `F` is undefined are *halting*.
  - A system is *complete* if it has no halting configurations.
  - A configuration `x` is *periodic* if `F^n(x) = x` for some `n ≥ 1`.
  - A complete system is *periodic* if every configuration is periodic.

## Theorems used

- **Theorem 3 (p. 423).** Periodicity of a given 2-RCM is undecidable. The reduction
  produces complete machines (the proof builds a complete 2-RCM `M'` that is periodic
  iff a given 2-RCM with mortal reverse is mortal). Input: Theorem 1 (immortality of
  2-RCM, from Hooper 1966 and Morita, TCS 168 (1996)).
- **Theorem 6 (p. 423).** It is undecidable whether a given complete 3-RCM, or a given
  (not necessarily complete) 2-RCM, admits a periodic configuration. Input: Morita's
  construction in TCS 168 (1996).
- For contrast, Theorems 2 and 4 show that uniform mortality and uniform periodicity
  of k-CM are decidable.

## Status of the source

The proofs in the paper are sketches; the authors say that page limits force this. The
theorems are published and widely cited. We use them as black boxes, and our node
depends on them exactly as stated above. No journal version was located.
