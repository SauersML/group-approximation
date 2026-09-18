---
rg: 2
id: computable-tree-involution-escapes-local-self-similar-hulls
kind: claim
title: For every uniformly computable family of injective level-local re-encodings of the binary tree, some computable involution of T_2 is sent by each of them outside every finitely generated self-similar group
distinct_from:
  computable-tree-groups-embed-in-fp-self-similar-groups: that is the open self-similar Higman characterization; this kills every proof of it that realizes the given computable action, or a re-encoding of it drawn from a fixed computable family, inside a finitely generated self-similar group. It does not refute that claim, because C_2 embeds in finitely presented self-similar groups through other actions.
  every-fp-rf-group-embeds-in-fp-self-similar-group: that is the flagship embedding question; this is an obstruction to one class of constructions for its second prerequisite.
  self-similar-hosts-contain-only-residually-finite-groups: that is an obstruction on the abstract group; this is an obstruction on the action, for the group C_2, which has no abstract obstruction at all.
  complexity-bounded-host-classes-are-not-universal: that diagonalizes word-problem time bounds against host classes; this diagonalizes tree portraits against finite section tables, and the input has trivial word problem.
---

**OPEN** (claimed via route [[computable-tree-involution-escapes-hulls-proof]];
returned to OPEN at landing on 2026-09-18 because the referee stage returned no
votes for this result, so it has not survived review. The proof is kept as an
attempt; see ## Attempts).

## Statement

Write `T_D` for the rooted tree on `Y_D^*`, `Y_D = {0, ..., D-1}`, and
`FR_D` for the set of automorphisms of `T_D` that lie in some finitely generated
self-similar subgroup of `Aut(T_D)`.

A **level-local re-encoding** is a map `iota : Aut(T_2) -> Aut(T_D)` together
with a computable `mu : N -> N` and a computable functional that returns the
action of `iota(g)` on `Y_D^{<=N}` from the action of `g` on `{0,1}^{<=mu(N)}`.
It need not be a homomorphism. A family `(iota_e, D_e, mu_e)_{e in N}` is
**uniformly computable** when these data are computable uniformly in `e`.

**Theorem.** Let `(iota_e)` be a uniformly computable family of injective
level-local re-encodings. Then there is an involution `g in Aut(T_2)`, computable
on vertices, with `iota_e(g) notin FR_{D_e}` for every `e`.

## Members of the family, each of which dies

The family can contain, all at once, every re-encoding in the following list,
for every `D >= 2`:

- **The identity and alphabet enlargements.** `Aut(T_2) -> Aut(T_D)` acts on
  words over `{0,1}` and fixes every vertex once a letter `>= 2` occurs.
- **Idle-level paddings along any fixed computable family of increasing
  functions** `f`, e.g. all primitive recursive ones. Here `g` acts on the
  letters in positions `f(1), f(2), ...` and fixes the letters in the other
  positions.
- **Conjugations by finite-state automorphisms and blockings** `T_2 -> T_(2^k)`,
  and any finite composites of these.

## Consequence for the self-similar Higman step

The input `(C_2, g)` satisfies every hypothesis of
[[computable-tree-groups-embed-in-fp-self-similar-groups]]. Its word problem is
trivial and its action is computable. So the following ways of proving that
claim fail at their first step, namely putting the given generators, after a
fixed re-encoding, inside a finitely generated self-similar group:

- **The self-similar closure of the given action**, Attempt 3 of
  [[every-fp-rf-group-embeds-in-fp-self-similar-group]] with its correction.
  Sections of `g` that are words over one finite section-closed set do not exist
  for this `g`.
- **Section words as a tape with a fixed schedule of idle levels**, Attempt 1 of
  [[computable-tree-groups-embed-in-fp-self-similar-groups]].
- **Any uniform recipe drawn from a computably enumerable list of total
  re-encodings.**

In every case the invariant is membership of the re-encoded generators in
`FR_D`, i.e. a finite section table. What remains possible is a re-encoding
chosen *as a function of the input*, for example idle levels scheduled by the
running time of the portrait algorithm. Diagonalization cannot reach those,
because the corresponding family of re-encodings is not uniformly total. A proof
of [[computable-tree-groups-embed-in-fp-self-similar-groups]], or of its first
half [[computable-tree-groups-embed-in-decidable-fg-self-similar-groups]], must
therefore re-encode the action in an input-dependent way. Higman's theorem does
the same when it re-encodes a recursive presentation through a Turing machine.

## Attempts

- **2026-09-18, diagonal against finite section tables (route
  [[computable-tree-involution-escapes-hulls-proof]]).** The worker claimed
  ESTABLISHED: enumerate the pairs (table, word), and at each stage for a pair
  `(e, n)` keep the candidate involution, with or without a new rigid swap far
  out on the spine, whose `iota_e`-image differs from the `n`-th table element
  below a level found by injectivity. Later swaps sit below `mu_e(L)`. *Referee
  reason for demotion:* the swarm-0917 referee stage returned no votes for this
  established result (votes lost), so it has not survived review. The proof file
  is kept unchanged as the attempt. Restore ESTABLISHED once a full referee pass
  survives.
