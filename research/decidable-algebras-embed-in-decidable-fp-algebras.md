---
rg: 2
id: decidable-algebras-embed-in-decidable-fp-algebras
kind: claim
title: Every finitely generated associative algebra with solvable word problem embeds in a finitely presented algebra with solvable word problem
distinct_from:
  clapham-fp-embedding-preserves-word-problem: that is Clapham's theorem for groups; this is the associative-algebra analogue, which no source in this graph states with the decidability clause.
  algebra-boone-higman-conjecture: that asks for a finitely presented simple envelope; this asks only for a finitely presented overalgebra with solvable word problem, which the root implies.
---

**OPEN.** Let `K` be a computable field. Every finitely generated associative
`K`-algebra with solvable word problem embeds in a finitely presented `K`-algebra
with solvable word problem.

This is the algebra form of Clapham's theorem for groups
(`clapham-fp-embedding-preserves-word-problem`).

## Where it sits

- **Necessary for the root.** `algebra-boone-higman-conjecture` implies it, via route
  `algebra-bh-implies-decidable-fp-overalgebras`: finitely presented simple algebras
  have solvable word problem.
- **Half of the root.** By `simple-ln-completion-premise-is-equivalent-to-algebra-bh`
  (part 2), the root is equivalent to this claim together with Boone--Higman for
  finitely presented algebras with solvable word problem.
- **Benchmark.** The monomial algebras `A_X = K<x,y>/(x y^n x : n in X)`, with `X`
  decidable of high complexity, are the hard inputs of
  `no-fp-simple-algebra-hosts-every-decidable-algebra`. This claim holds for them:
  `monomial-algebras-embed-in-decidable-fp-algebras` (2026-09-13) covers every
  finitely generated monomial algebra with solvable word problem.

## Literature

- **Belyaev's associative Higman theorem (read 2026-09-13).** V. Ya. Belyaev,
  *Subrings of finitely presented associative rings*, Algebra i Logika 17 (1978),
  no. 6, 627--638; English translation in Algebra and Logic 17 (1978), 407--414,
  DOI 10.1007/BF01673571. Read from the Springer scan, text extracted with
  `pdftotext`. Most formulas are lost in extraction; the prose is legible.
  - **Statement.** "Suppose that K is either a commutative associative finitely
    generated ring with unity or a finitely generated extension of a prime field.
    We will show that any associative K-algebra with a recursively enumerable set
    of defining relations can be embedded in a finitely presented associative
    K-algebra." Also: "The unity of an algebra, if there is one, is not fixed in
    the signature."
  - **Proof structure.**
    - *Lemma 1.* Given a `K`-module endomorphism that is a homomorphism on a
      finitely generated subalgebra, it adjoins solutions of a system of
      equations in an overalgebra. The ring case is credited to Taitslin.
    - *Lemma 2.* It embeds an algebra with a recursively enumerable presentation
      of a special form in one whose relations are, except one, word equalities.
    - *Lemma 3.* A modification of Mal'tsev's theorem: a countable algebra
      `{a_1, a_2, ...}` sits in an algebra with elements `a, b, c` such that
      `a_i = a b^i c`.
    - *The theorem.* Its proof applies Murskii's semigroup embedding theorem
      (Mat. Zametki 1 (1967), 217--224) twice and Lemma 1 three times.
  - **Decidability.** The paper never mentions the word problem. Its only uses of
    "solvable" refer to systems of equations. This agrees with the secondary quote
    in the Gröbner--Shirshov survey of Bokut and Chen (arXiv:1303.5366): "For
    associative algebras a similar problem [21] was solved positively by
    V. Y. Belyaev [10]."
- **Semigroups (statement from the abstract).** Birget 1998, Internat. J. Algebra
  Comput. 8, 235--294. Every finitely generated semigroup with solvable word
  problem embeds in a finitely presented semigroup with solvable word problem, by a
  conjunctive linear-time reduction of word problems. It is imported as
  `birget-semigroup-embedding-preserves-word-problem`, which quotes the abstract.
  The paper body was not accessible.

## Attempts

1. **Direct finite complete rewriting system for `A_X`** (2026-09-13). Adjoin head letters
   and a trigger rule `x y -> x h_0 y` that runs a total decider for `X` on the `y`-block
   and produces `0` on acceptance. Acceptance kills exactly the words containing
   `x y^n x`, `n in X`.
   - *Superseded for `A_X` by attempt 2; confluence was never settled.* The
     simulation keeps the `x, y` skeleton, so distinct basis words keep distinct
     normal forms.
   - The difficulty is global confluence and termination on arbitrary words over
     the enlarged alphabet: several heads, heads meeting the trigger (the overlap
     `h_q x y`), and heads at the end of a word.
2. **Through contracted semigroup algebras** (2026-09-13). *Works for monomial
   algebras* (`monomial-algebras-embed-in-decidable-fp-algebras`).
   - **The zero problem is avoided.** The earlier blocker was the need for a
     semigroup theorem that preserves the zero. Instead, embed the monoid with zero
     `M` in Birget's envelope `H` by `phi`, set `e = phi(0)`, and map
     `m -> phi(m) - e` inside `K[H^1]`. This kills `0`, it is multiplicative
     because `e` absorbs `phi(M)`, and it is injective because `phi` is. Adding a
     character times `1 - phi(1) + e` makes it unital.
   - *Dies for general algebras.* A general finitely generated algebra is not a
     contracted monoid algebra. No embedding of an arbitrary algebra with solvable
     word problem into a contracted monoid algebra with solvable word problem is
     known here.
3. **Belyaev's construction with Birget in place of Murskii** (2026-09-13,
   refined). The full paper was read at source (`belyaev-associative-higman-theorem`,
   artifact `belyaev-1978-decidability-analysis-2026-09-13`), and this route is now
   a wired reduction, `decidable-clapham-via-effective-belyaev`. It reduces (C) to
   exactly two open holes, with three ingredients proved:
   - **Proved.** The coordinating data (enumeration, the set `Y`, and the counting
     functions `f, g`) is computable, so `S` and the two Murskii semigroups have
     recursive relation sets (`belyaev-embedding-relations-are-recursive-for-decidable-input`);
     the semigroup algebra of a decidable semigroup is decidable
     (`semigroup-algebra-of-decidable-semigroup-is-decidable`); Birget already
     preserves the word problem. `K = F_p`, `Q`, and any decidable field finitely
     generated over its prime field are covered.
   - **Gap 1** (`belyaev-murskii-semigroups-have-solvable-word-problem`, OPEN). The
     two semigroups fed to Murskii need *solvable* word problem, not merely
     recursive relations, for Birget to replace Murskii. Markov–Post shows
     recursive relations are not enough; the single-power-block shape of the
     relations is the lever, but confluence was not proved.
   - **Gap 2** (`belyaev-lemma-one-preserves-word-problem`, OPEN). Lemma 1's
     overalgebra must keep a solvable word problem; the rank induction reads as a
     confluence argument for an explicit rewriting, but a full termination and
     confluence proof was not supplied.

   So (C) is no longer "recheck the whole paper": it is these two concrete,
   self-contained lemmas.
