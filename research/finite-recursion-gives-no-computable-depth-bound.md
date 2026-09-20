---
rg: 2
id: finite-recursion-gives-no-computable-depth-bound
kind: claim
title: For a functionally recursive (finite-recursion self-similar) group the word problem is decidable iff its nontriviality depth is bounded by a computable function; Bartholdi–Mitrofanov's functionally recursive group with non-recursive word problem, which is automatically residually W_d, therefore shows that finite recursion plus residually-W_d forces no computable depth bound, so the structure-group channel of gate 1 via Farley–Hughes can only be capped by finite presentation
distinct_from:
  farley-hughes-certificates-have-prefix-chart-coordinates: that reduces gate 1 via FH (nested and product certificates) to the word problems of finitely recursive, residually-W_d structure groups; this shows those two properties alone give no computable bound on their nontriviality depth, so that channel is not closed by them.
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that is the open target (finitely presented self-similar groups beyond every recursive bound); this shows finite presentation is the only remaining possible cap, since finite recursion and residual W_d allow depth beyond every computable function.
  computable-tree-groups-embed-in-decidable-fg-self-similar-groups: that asks for decidable finitely generated self-similar hosts and quotes the same Bartholdi–Mitrofanov abstract as a warning; this uses their existence theorem A'' to settle a depth-bound question.
---

**ESTABLISHED (lane bh-gate1-abstract, 2026-09-19; elementary, plus one verbatim-cited theorem).**
Referee bh-ref-t0 PASS (14b9c876b6). One wording fix is applied: a uniform bound *implies* the negation of the
hard-WP target and is not equivalent to it.

**Correction (2026-09-19).** As printed in the arXiv versions, Bartholdi–Mitrofanov's Theorem A″ rests on their Proposition 2.4, whose proof has a gap. There `[g,u] ≠ 1` for every machine. It is repaired by replacing `u` with a partner `p` supported on `0^*1A^ω`; see `bartholdi-mitrofanov-proposition-2-4-gap-and-repair` (referee bh-ref-f PASS, 6747a7e43d). Theorem A″ holds for the repaired table `G′_M = ⟨Φ_M, p, p′⟩`. This node uses only that some faithful functionally recursive group has a non-recursive word problem. The repaired group is one, so every conclusion here stands.

## Setting

- **Functionally recursive groups.** A finite map `Φ: A × S → F_S × A` defines a group `G = ⟨Φ⟩`, where `S` is a
  finite generating set, `F_S` the free group on it, and `A` a finite alphabet. `G` is the faithful quotient of
  `F_S` acting on `A*`, each generator rewriting the first letter and applying a word to the rest.
  - Up to choosing `S`, these are exactly the finitely generated self-similar groups with finite recursion.
    Taking the one-type chart graph, this is also the recursion of item 3 of
    `farley-hughes-certificates-have-prefix-chart-coordinates`.
- **Depth.** `D(n)` is the maximum, over words `w` of length `≤ n` with `w ≠ 1` in `G`, of the least level at
  which `w` moves a vertex.

## Statement

1. `G ≤ Aut(T_(|A|))`, so `G` is residually `W_(|A|)`, i.e. (N1) of
   `every-fp-rf-group-embeds-in-fp-self-similar-group`.
2. `WP(G)` is decidable **iff** `D` is bounded by a computable function, and then `D` is itself computable.
3. **Bartholdi–Mitrofanov**, arXiv:1710.10109, Theorem A″, quoted from the paper: "There is a functionally
   recursive group ⟨Φ⟩ with Φ:A×S→FS×A such that {s∈FS∣s=1 in ⟨Φ⟩} is not recursive." (The abstract reads: "We
   prove that the word problem is undecidable in functionally recursive groups, and that the order problem is
   undecidable in automata groups, even under the assumption that they are contracting.")
4. **Consequence.**
   - Finite recursion together with residual `W_d` implies **no** computable bound on `D`.
   - That group has depth beyond every computable function.
   - It is not finitely presented: its word problem would then be r.e. and co-r.e., hence decidable.

## Proof

- **1.** The group acts faithfully on `A*`. Its level-`k` quotients are subgroups of the `k`-fold iterated wreath
  product of `S_(|A|)`, and they separate points.
- **2, "if".** The level-`k` action of a word is computable from `Φ`, since its sections at level `k` have length
  `≤ L^k |w|`. If `w ≠ 1`, then `w` moves a vertex at level `≤ D(|w|) ≤ F(|w|)`, and hence at level `F(|w|)`
  itself. So `w = 1` iff `w` fixes level `F(|w|)`, which is decidable.
- **2, "only if".** List the words of length `≤ n`, discard the trivial ones with the decision procedure, and for
  each remaining word search the levels in order for a moved vertex. The search terminates by faithfulness. Then
  `D(n)` is the maximum of these levels.
- **4.** Apply 2 to Theorem A″. ∎

## What this means for gate 1 via Farley–Hughes

- **The outright closure fails.** The coordinator asked whether "finite recursion + residually `W_d`" already
  forces a computable depth bound, which would kill the structure-group channel and close gate 1 via FH. It does
  not.
- **The only possible cap is finite presentation.** FH's Prop. 8.10 needs type `F_n`, `n ≥ 2`, of the structure
  groups.
  - A finitely presented functionally recursive group has decidable word problem, so its `D` is computable. That
    is a bound for each group separately.
  - A **uniform** recursive bound over all of them would be a new theorem, and it would imply the negation of
    `fp-self-similar-groups-with-arbitrarily-hard-word-problem`.
  - In the multi-type chart setting, the family `(H_τ)` must be finitely presented type by type.
- **Where the tension sits.**
  - Finite recursion permits unbounded, even non-computable, depth. Finite presentation forces decidability.
  - Hard examples must be finitely presented functionally recursive groups whose relators are consistent with
    delays in nontriviality detection that grow beyond `T`.
  - Bartholdi–Mitrofanov's group shows the delays are available. Whether they survive finite presentation is the
    whole question.

## Lesson for general BH

**Finite recursion does not bound depth; only finite presentation might.** Functionally recursive groups can hide
nontriviality arbitrarily deep, beyond computability (Bartholdi–Mitrofanov A″). So the last hardness channel of
Farley–Hughes engines is exactly "finite presentation versus deep delays". The channel is neither dead nor
supplied.
