---
rg: 2
id: decidable-fg-self-similar-groups-embed-in-fp-self-similar
kind: claim
title: Every finitely generated self-similar group with solvable word problem embeds in a finitely presented self-similar group
distinct_from:
  computable-tree-groups-embed-in-fp-self-similar-groups: that takes any finitely generated group with a computable tree action; this takes only groups that are already self-similar with a finite section table. It is that claim restricted to its own natural inputs, the r.e. half, and is implied by it.
  computable-tree-groups-embed-in-decidable-fg-self-similar-groups: that is the other half, producing a finitely generated self-similar host; this turns such a host into a finitely presented one.
  fp-self-similar-groups-embed-in-fp-simple-groups: that embeds finitely presented self-similar groups in finitely presented simple groups; this asks for the Higman step that would feed it finitely generated self-similar inputs.
  every-decidable-group-embeds-in-fp-self-similar-group: that is refuted because its inputs need not be residually finite; the inputs here are self-similar and hence residually finite.
---

**OPEN.** Let `S <= Aut(T_d)` be finitely generated and self-similar, with
solvable word problem. Then `S` embeds in a finitely presented self-similar
group.

## Necessity (established here)

`S` is named by a finite section table (Step 1 of
[[computable-tree-involution-escapes-hulls-proof]]), so its action on `T_d` is
computable, and its word problem is solvable by hypothesis. So `S` satisfies the
hypotheses of [[computable-tree-groups-embed-in-fp-self-similar-groups]], and
that claim implies this one. The hypothesis on the word problem is necessary, by
the necessity section of that claim.

## Why this is the r.e. half

This is Higman's embedding theorem, moved into the self-similar category.

- **Relations.** A finitely generated self-similar group has co-r.e. relations,
  read off its table. A solvable word problem makes them recursive, which is the
  input Higman's theorem needs.
- **What stays open.** No construction is known that keeps self-similarity
  through Higman's steps: an HNN extension, a Britton-type free construction,
  then finite presentation.
- **Self-similar hosts are rigid.**
  [[self-similar-hosts-contain-only-residually-finite-groups]] shows they contain
  only residually finite groups, so the non-residually-finite Higman
  constructions cannot be copied. `rf-higman-embedding-for-decidable-groups` is
  refuted by Rauzy's effective residual finiteness invariant, but that invariant
  does not apply here: `S` is effectively residually finite through its level
  quotients.

## Test inputs

The graph records no finitely presented self-similar overgroup for any of these.

- **Contracting automata groups**, e.g. the first Grigorchuk group and the
  Basilica group. They are finitely generated, self-similar and not finitely
  presented, with polynomial-time word problem.
  - These already satisfy Boone--Higman through Nekrashevych's FP2 in
    [[rover-nekrashevych-finite-presentation-criteria]]. That uses a
    Rover--Nekrashevych host, not a finitely presented self-similar one.
  - So they test this claim itself, not its Boone--Higman consequence.
- **Functionally recursive groups with solvable word problem above a given
  recursive time bound.** The graph does not establish that they exist. If they
  do, this claim embeds each of them in a finitely presented self-similar group,
  whose word problem is at least as hard. That gives
  [[fp-self-similar-groups-with-arbitrarily-hard-word-problem]].

## Where it can fail

A counterexample is a finitely generated self-similar group with solvable word
problem that lies in no finitely presented self-similar group. By the halving
route [[computable-tree-embedding-via-decidable-self-similar-hulls]], it would
refute [[computable-tree-groups-embed-in-fp-self-similar-groups]] directly,
whatever happens to the first half.

## Attempts

1. **Run Higman's construction and hope the result is self-similar (2026-09-17,
   dead as stated).** Higman's embedding of a recursively presented group into
   a finitely presented one uses amalgamated products and HNN extensions along
   benign subgroups. It gives no control on residual finiteness.
   - *Where it dies.* The step where the output would have to lie in
     `Aut(T_D)`. Every subgroup of a self-similar host is residually finite
     ([[self-similar-hosts-contain-only-residually-finite-groups]]), and the
     construction has no mechanism ensuring this.
   - *Why the general version is false.* `rf-higman-embedding-for-decidable-groups`
     is refuted by Rauzy, so no construction can preserve residual finiteness
     for all finitely generated residually finite inputs with solvable word
     problem.
   - *What the inputs here have extra.* A finite section table. An attack must
     use the table, not only the relations.
2. **Rover--Nekrashevych detour (2026-09-17, deferred).** For contracting `S`,
   FP2 of [[rover-nekrashevych-finite-presentation-criteria]] makes `V_d(S)`
   finitely presented. That host is not residually finite, hence not
   self-similar, so it proves Boone--Higman for `S` and not this claim.
   Extracting a finitely presented self-similar subgroup of `V_d(S)` containing
   `S` is not attempted.

3. **A hard test input** (bh-free-02, 2026-09-18). The Wächter--Weiß automaton groups
   (arXiv:1906.03424v3) have PSPACE-complete word problem. For a finite conjunction
   group `R`, such as `A_5`, the group `G_R` is locally-finite-by-`Z` and not finitely
   presented (`finite-commutator-wachter-weiss-groups-are-not-fp`).
   - *Why it matters.* Any finitely presented self-similar overgroup of `G_R` would
     have PSPACE-hard word problem. Through
     `fp-self-similar-groups-embed-in-fp-simple-groups` it would give a finitely
     presented simple group beyond Birget's coNP.
   - *Hosts excluded, unless PSPACE = coNP.* The overgroup cannot lie in a
     piecewise prefix-and-automaton host over coefficient groups with
     polynomial-time word problem
     (`automaton-tail-full-groups-have-conp-relative-word-problem`). That rules out
     `V_d(S)` for contracting `S`.
   - *Status.* Untried.
