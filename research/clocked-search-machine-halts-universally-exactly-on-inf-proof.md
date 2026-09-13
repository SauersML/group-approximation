---
rg: 2
id: clocked-search-machine-halts-universally-exactly-on-inf-proof
kind: route
title: Unbounded search over a monotone primitive recursive predicate, compiled from LOOP code that terminates from any state
target: clocked-search-machine-halts-universally-exactly-on-inf
requires: []
artifacts:
  - research/artifacts/rf-fp-pumped-minsky-part3-2026-09-12.md
---

The full proof is Lemma C (Section 6) of
`research/artifacts/rf-fp-pumped-minsky-part3-2026-09-12.md`.

1. `W_(e,s) = {x < s : phi_e(x) halts within s steps}` is primitive recursive
   in `(e, s)` and increases with `s`.  So `Phi(e,s,n) = [|W_(e,s)| > n]` is a
   LOOP-computable predicate, monotone in `s`, and `e in INF` iff
   `forall n exists s Phi(e,s,n)`.
2. Compile LOOP code with draining loops, and give each `LOOP X DO P END` a
   fresh counter that `P` never touches.  By induction on program structure,
   every construct entered anywhere, with any register contents, exits.
   Inserting clock commands changes nothing.
3. *INF.*  From any configuration the machine reaches `L0` or stop.  From `L0`,
   each round computes `Phi` correctly on the current `S, N` (rewriting `E`,
   restoring `S, N`) and increments `S`.  Monotonicity makes some round
   succeed, so the machine stops.
4. *FIN.*  With `|W_e| = k`, the configuration at `L0` with `N = k` and all
   other registers `0` computes `Phi(e, s, k) = 0` in every round, forever.
