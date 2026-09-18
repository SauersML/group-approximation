# Salo 2020/2022: source record for the 21.73 discussion

Lane bh-free-58. This file records what was read at source, for
`ct-z-finite-subgroups-are-classified-by-stabilizer-sets`.

- **Source.** V. Salo, "Conjugacy of reversible cellular automata and one-head machines",
  arXiv:2011.07827v2. The TeX source (`AutConjugacyOnly2.tex`) is in the swarm scratchpad at
  `gq/src/bh-free-58/salo/main.tex`. Read: the introduction and main results, Lemma
  `lem:Mn`, Section "What to do when the nth program halts", Lemma `lem:b`, and Section
  "Conjugacy for 2V and Turing machines".
- **Theorem `thm:2V`, paraphrased.** For `G = 2V`, or a Turing machine group `RTM(s,q)`
  with nontrivial tape alphabet, there are computable `α, β : N → G` such that the
  following are equivalent:
  - the nth program halts;
  - `α(n)` and `β(n)` have finite order;
  - they are conjugate by an involution;
  - they are conjugate.
- **Mechanism.**
  - `α(n)` and `β(n)` simulate the same one-head machine `M_n`, which is periodic iff the
    program halts (Kari–Ollinger 2008, Thm 8). The two elements differ only in that
    `β(n)` flips a "blinker" bit when the head touches it.
  - **Halting case.** Orbits have bounded period, so a clopen cross-section of the orbits
    gives an involutive conjugator that adjusts the blinker bits.
  - **Non-halting case.** A long excursion flips a far-away blinker, and a bounded-range
    conjugator cannot account for that flip.
- **Relevance.** The yes-instances have finite order. See the node for why this cannot
  transfer to `CT(Z)`.
