---
rg: 2
id: type-f-group-receives-re-languages-by-pattern-reductions
kind: claim
title: A type F group receives every r.e. language, and every recursively presented word problem, by one-homomorphism four-occurrence pattern reductions
distinct_from:
  some-type-f-group-has-re-complete-word-problem: That is completeness under arbitrary many-one reductions, whose reducing function for G_M produces words of exponential length; this is completeness under the far finer pattern reductions v -> omega(phi(v)) with phi one free-monoid homomorphism, for a different type F group H_M, and it adds the obstruction consequence for Zaremsky 1.1 at the level of every reducibility containing pattern reductions.
  complexity-bounded-host-classes-are-not-universal: That excludes inputs from host classes with a recursive time bound on the HOST's word problem; this is about reductions INTO one fixed host with no time bound on its word problem, and shows that the cost of the reduction, as opposed to the cost of the host's algorithm, separates nothing.
  quantitative-higman-embedding-with-dehn-control: That embeds a time-bounded input into a finitely presented host with Dehn control (an embedding, needs a decidable input); this is a reduction, not an embedding, for arbitrary r.e. inputs, into a host of type F.
artifacts:
  - experiments/boone-pattern-reductions-2026-09-17/check_pattern_words.py
  - experiments/boone-pattern-reductions-2026-09-17/results.txt
---

**ESTABLISHED (proposed, 2026-09-17; referee welcome).** Let `M` be the
modular machine compiled, through the machine-checked chain of
`some-type-f-group-has-re-complete-word-problem`, from a universal
`ToPartrec` code. Let `m = M.size >= 2` and let `G_M = <..., t, x, y, k, ...>`
be its final Aanderaa--Cohen--Boone group. Put

    H_M = < G_M, s | s^-1 t s = t,  s^-1 x s = x,  s^-1 y s = y^m >.

1. **Type F.** `H_M` is an HNN extension of `G_M` along the base group
   `<t,x,y> ≅ Z * Z^2` and its injective endomorphism `t -> t, x -> x, y -> y^m`.
   It is finitely presented, has a finite `K(H_M,1)` of dimension at most 3,
   and contains `G_M`.
2. **Pattern completeness.** Let `A` be a finite alphabet. There is a
   free-monoid homomorphism `phi : A* -> F(gens H_M)`, depending only on `A`
   and `M`, with the following property. For every r.e. `L ⊆ A*` there is a
   word `omega_L(X)` in the generators of `H_M` and one variable `X`, in which
   `X` occurs exactly four times (twice as `X`, twice as `X^-1`), such that for
   every `v ∈ A*`

       v ∈ L   <=>   omega_L(phi(v)) = 1 in H_M.

   Here `phi(a)` is a fixed word of length `O(log |A|)`. The reduction has
   linear size and runs in linear time.
3. **Word problems.** In particular, the word problem of every finitely
   generated recursively presented group `G` (a language over its generators
   and their inverses) reduces to the word problem of `H_M` in this way.
4. **Lemma E (one occurrence is embedding).** Suppose that for an ARBITRARY
   monoid homomorphism `phi` and fixed words `P` and `Q`, `v = 1` in `G` iff
   `P phi(v)^{±1} Q = 1` in `H`. Then `a -> phi(a)^{±1}` is an injective
   homomorphism `G -> H`. Conversely every embedding is such a reduction.

**Consequence for Zaremsky Problem 1.1 (a class-killing obstruction).** A
"word-problem obstruction" through a reducibility `R` exhibits a `G` whose word
problem is `R`-reducible to the word problem of no group of type `F_{n+1}`, and
concludes that `G` has no type `F_{n+1}` host. Such an obstruction can succeed
only on groups already excluded by r.e.-ness, and which therefore embed in no
finitely presented group, when `R` contains the one-homomorphism
four-occurrence patterns. Examples of such `R`: linear-time, linear-size,
polynomial-time and log-space many-one reductions, for every `n` at once. This
kills the "time complexity of the reduction" refinement proposed in
`some-type-f-group-has-re-complete-word-problem`.

At one occurrence (Lemma E), the relation "`WP(G)` reduces to `WP(H)` for some
`H` of type `F_{n+1}`" IS Problem 1.1. So a word-problem-reduction obstruction
must use patterns with 2 or 3 occurrences, which is the open window. For two
occurrences it is a letter-local reduction of `WP(G)` to membership in a
centralizer `C_H(Q)`. The alternative is to couple the reduction with an
invariant of the host.

What this does not address: invariants of the host itself (Dehn function,
isoperimetric spectrum, `L^2` invariants), which are not reductions. The Dehn
function is not monotone under embeddings (Birget--Ol'shanskii--Rips--Sapir),
so it needs its own monotonicity device.

Proof: route `type-f-group-receives-re-languages-by-pattern-reductions-proof`.
The Horner identity and the letter-for-letter pattern form are also checked on
3000 random instances by
`experiments/boone-pattern-reductions-2026-09-17/check_pattern_words.py`.
