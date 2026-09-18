---
rg: 2
id: computable-tree-groups-embed-in-decidable-fg-self-similar-groups
kind: claim
title: Every finitely generated group with solvable word problem and a computable faithful regular-tree action embeds in a finitely generated self-similar group with solvable word problem
distinct_from:
  computable-tree-groups-embed-in-fp-self-similar-groups: that asks for a finitely presented self-similar host; this asks only for a finitely generated self-similar host with solvable word problem. It is the co-r.e. half of that claim and is implied by it.
  decidable-fg-self-similar-groups-embed-in-fp-self-similar: that is the other half, a self-similar Higman theorem for finitely generated self-similar inputs; this builds such an input around a group given only by a computable action.
  computable-tree-involution-escapes-local-self-similar-hulls: that shows the host cannot be obtained by keeping the given action, or by a fixed computable re-encoding of it; this is the statement a non-uniform re-encoding would have to prove.
---

**OPEN.** Let `H` be a finitely generated group with solvable word problem and
a faithful action on some `T_d` (`d >= 2`) that is computable on vertices. Then
`H` embeds in a finitely generated self-similar group `S <= Aut(T_D)`, for some
`D`, and `S` has solvable word problem.

## Necessity (established here)

**It is implied by the full claim.** Suppose
[[computable-tree-groups-embed-in-fp-self-similar-groups]] gives `H <= P` with
`P` finitely presented and self-similar. Then `P` is finitely generated. It is
residually finite, by [[self-similar-hosts-contain-only-residually-finite-groups]].
By McKinsey's algorithm, as recorded in that claim's necessity section, `P` has
solvable word problem. So `S = P` works.

**Both hypotheses are necessary.** Let `S` be finitely generated and
self-similar with solvable word problem, and let `H <= S` be finitely generated.
By Step 1 of [[computable-tree-involution-escapes-hulls-proof]], `S` is named by a
finite table, so its action is computable. `H` inherits a computable faithful
action and a solvable word problem.

## Why this is the co-r.e. half

- **What a table gives.** A finitely generated self-similar group comes with a
  finite section table, so its action is computable and its word problem is
  co-r.e.: a nontrivial word is detected by finding a vertex it moves.
- **The word problem can still be undecidable.** Bartholdi--Mitrofanov,
  arXiv:1710.10109, abstract: "We prove that the word problem is undecidable in
  functionally recursive groups, and that the order problem is undecidable in
  automata groups, even under the assumption that they are contracting." Here
  functionally recursive groups are the finitely generated self-similar groups
  named by finite tables. So the requirement of a solvable word problem on `S`
  is a real condition.
- **Complexity is not the obstacle.** Finitely generated self-similar groups
  simulate machines, as that abstract shows. Solvable-word-problem hosts beyond
  every recursive bound are allowed, since (N2) of
  [[every-fp-rf-group-embeds-in-fp-self-similar-group]] rules out only
  finite-state generators.
- **The obstacle is the section table.**
  [[computable-tree-involution-escapes-local-self-similar-hulls]] gives a
  computable involution `g` of `T_2` that no fixed computable re-encoding places
  in any finitely generated self-similar group. A proof must re-encode the input
  action in a way that depends on the input, e.g. idle levels scheduled by the
  portrait algorithm's running time. It must also keep the word problem of the
  resulting host decidable.

## Where it can fail

A counterexample is an effectively residually finite finitely generated group
`H`, with a computable faithful tree action, such that every finitely generated
self-similar group containing `H` has undecidable word problem, or no such group
exists at all.

- **The count does not stop it.** There are countably many finitely generated
  self-similar groups, and countably many groups satisfying the hypotheses, so
  cardinality gives no obstruction.
- **The diagonal argument does not stop it.** The argument of
  [[computable-tree-involution-escapes-hulls-proof]] needs a computable list of
  total re-encodings. It does not apply to re-encodings chosen from the input.

## Attempts

1. **Keep the given action, or apply a fixed re-encoding (2026-09-17, dead).**
   The approach: take the self-similar closure of the given generators, possibly
   after alphabet enlargement, a fixed idle-level schedule or a finite-state
   conjugation.
   - *Where it dies.* The first step fails: the re-encoded generators must have
     sections forming words over one finite table.
   - *Why.* [[computable-tree-involution-escapes-local-self-similar-hulls]] gives
     a computable involution for which this fails, simultaneously for every
     member of any computable list of injective level-local re-encodings.
2. **Idle levels scheduled by the input's running time (2026-09-17, sketch
   only).** Pad `T_d` with blocks of idle levels whose lengths grow with the
   running time of the portrait algorithm. Let finitely many table generators
   simulate that algorithm on the section word over the idle block, as in
   Attempt 1 of [[computable-tree-groups-embed-in-fp-self-similar-groups]].
   - *Where it stalls, first.* A self-similar generator can only permute letters.
     Any scratch computation written on idle letters moves vertices, so the
     copy of `H` is not simply the padded action.
   - *Where it stalls, second.* Different paths through the idle blocks carry
     different, possibly ill-formed, tape contents. The generators must act
     trivially or consistently on all of them.
   - *Where it stalls, third.* Deciding the word problem of the resulting table
     group requires controlling what the generators do on ill-formed tapes. This
     is exactly where Bartholdi--Mitrofanov obtain undecidability.
