---
rg: 2
id: common-decidable-hosts-iff-uniform-word-problem
kind: claim
title: A class of finite presentations has a common finitely generated host with solvable word problem iff its word problem is uniformly solvable; under Boone-Higman such a c.e. class has one finitely presented simple host with computable embeddings
distinct_from:
  fp-simple-envelopes-not-computable-from-presentations: that rules out computing an envelope from a presentation for two specific classes; this characterizes, for every c.e. class, exactly when a common or uniformly computable envelope exists (uniform word problem), and says Boone-Higman already supplies one whenever it does.
  countable-decidable-groups-embed-in-fp-simple-groups: that is the countable-input form of Boone-Higman for one countable group; this applies that form to the free product of a whole c.e. class, and adds the converse (a common decidable host forces a uniform word problem).
  simple-envelope-forces-solvable-word-problem: that deduces a solvable word problem for one subgroup of one finitely presented simple group; this runs the same semi-decision uniformly over a class and over all candidate embeddings, so that it needs no embedding as input.
  boone-higman-conjecture: that asks for one envelope per input; this shows that the apparently stronger universal and uniform forms, over any c.e. class with uniformly solvable word problem, are consequences of it.
---

**ESTABLISHED** (lane proof, not reviewed; route
`common-decidable-hosts-iff-uniform-word-problem-proof`). Elementary; no priority
claimed. Part 1 is the classical Boone--Rogers-style semi-decision, and parts 2 and 3
combine standard embedding theorems.

Let `𝒞` be a set of finite presentations, and write `G_P` for the group of `P`. Say
the word problem is **uniformly solvable on `𝒞`** if one algorithm, given `P ∈ 𝒞`
and a word `w` in the generators of `P`, decides whether `w = 1` in `G_P`.

1. **A common decidable host forces uniformity (any class).** Suppose some finitely
   generated group `H` with solvable word problem contains a copy of every `G_P`,
   `P ∈ 𝒞`. Then the word problem is uniformly solvable on `𝒞`. The algorithm needs
   only `P` and `w`, not the embeddings. In particular this holds when `H` is a
   finitely presented simple group.
2. **Uniformity gives a common decidable host (c.e. classes, unconditional).** If
   `𝒞` is recursively enumerable and the word problem is uniformly solvable on `𝒞`,
   then some finitely presented group `K` with solvable word problem contains every
   `G_P`. The embeddings `G_P -> K` are computable from `P`, as words for the
   generators of `P`.
3. **Boone--Higman gives a common simple host.** If `boone-higman-conjecture` holds,
   then for every such c.e. class there is ONE finitely presented simple group `S`
   containing every `G_P`, with embeddings `G_P -> S` computable from `P`.
4. **Characterization.** Assume Boone--Higman, and let `𝒞` be c.e. The following
   are equivalent:
   - (a) the word problem is uniformly solvable on `𝒞`;
   - (b) one finitely presented simple group contains every `G_P`;
   - (c) some algorithm computes from each `P ∈ 𝒞` a finite presentation of a simple
     group `S_P` and an embedding `G_P -> S_P`. Here the hosts may vary with `P`.

   Without Boone--Higman, (a) is still equivalent to having a common finitely
   presented host with solvable word problem, by parts 1 and 2. Also (b) ⇒ (a) and
   (c) ⇒ (a) hold unconditionally.
5. **Equivalent universal form.** Boone--Higman holds if and only if every c.e.
   class of finite presentations with uniformly solvable word problem has a common
   finitely presented simple host. For ⇐, apply it to singleton classes.

## Corollaries

- **No universal decidable host** (classical; Boone--Rogers). No finitely generated
  group with solvable word problem, and so no finitely presented simple group,
  contains every finitely presented group with solvable word problem. Uniform
  solvability fails on that class.
- **No universal host even at fixed low complexity.** No finitely generated group
  with solvable word problem contains every group `H_e` of
  `polynomial-dehn-fp-groups-have-nonuniform-word-problem`. In particular, no
  finitely presented simple group contains every finitely presented group with
  Dehn function `≼ n^18`. The same holds for every finitely presented group whose
  word problem is decided in time `2^((n+1)^37)`. By part 1 and item 4 of that node,
  a common host would decide the halting problem.
- **Unconditional common decidable hosts.** The following classes are c.e. and
  have uniformly solvable word problem. So each has one finitely presented host
  with solvable word problem, with computable embeddings:
  - **hyperbolic groups.** Hyperbolicity is semi-decidable (Papasoglu 1996), and
    Dehn's algorithm is uniform once a hyperbolicity constant is found by that
    search;
  - **one-relator groups** (Magnus; the algorithm is uniform in the relator).

  Citations are textbook-level and were not read at source for this node.
- **Conditional universal simple hosts.** Under Boone--Higman, there is one
  finitely presented simple group containing every hyperbolic group, and one
  containing every one-relator group. Unconditionally this is OPEN. Belk--Bleak--
  Matucci--Zaremsky embed each hyperbolic group separately, and no universal host
  is recorded on main. Finite subgroups do not obstruct it: a finitely presented
  simple group can contain every finite group, since `V` does.

## What this changes for Boone--Higman work

- A proof of Boone--Higman may be non-uniform, but on every c.e. class with
  uniformly solvable word problem it is automatically uniform (parts 3 and 4). So
  "universal" strengthenings, such as one host for all hyperbolic groups, are
  corollaries of the conjecture, not strengthenings of it.
- The only place a Boone--Higman proof must be non-uniform is across inputs whose
  word problems are not uniformly solvable. There the envelope must consume the
  decision procedure or equivalent finite data, as in
  `fp-simple-envelopes-not-computable-from-presentations`. Whether it can always be
  computed from a decision procedure is `boone-higman-uniform-in-word-problem-algorithms`
  (OPEN).
