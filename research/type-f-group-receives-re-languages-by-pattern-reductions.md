---
rg: 2
id: type-f-group-receives-re-languages-by-pattern-reductions
kind: claim
title: A type F group receives every r.e. language, and every recursively presented word problem, by linear-size two-homomorphism pattern reductions
distinct_from:
  some-type-f-group-has-re-complete-word-problem: That is completeness under arbitrary many-one reductions, whose reducing function for G_M produces words of exponential length; this is completeness under the far finer pattern reductions v -> omega(phi(v), psi(v)) with phi, psi free-monoid homomorphisms, for a different type F group H_M, and it adds the obstruction consequence for Zaremsky 1.1 at the level of every reducibility containing pattern reductions.
  complexity-bounded-host-classes-are-not-universal: That excludes inputs from host classes with a recursive time bound on the HOST's word problem; this is about reductions INTO one fixed host with no time bound on its word problem, and shows that the cost of the reduction, as opposed to the cost of the host's algorithm, separates nothing.
  quantitative-higman-embedding-with-dehn-control: That embeds a time-bounded input into a finitely presented host with Dehn control (an embedding, needs a decidable input); this is a reduction, not an embedding, for arbitrary r.e. inputs, into a host of type F.
artifacts:
  - experiments/boone-pattern-reductions-2026-09-17/check_pattern_words.py
  - experiments/boone-pattern-reductions-2026-09-17/results.txt
---

**ESTABLISHED (proposed, 2026-09-17; referee welcome).** Let `M` be the
modular machine compiled, through the machine-checked chain of
`some-type-f-group-has-re-complete-word-problem`, from a universal
`ToPartrec` code, let `m = M.size >= 2` and let `G_M = <..., t, x, y, k, ...>`
be its final Aanderaa--Cohen--Boone group. Put

    H_M = < G_M, s | s^-1 y s = y^m >.

1. **Type F.** `H_M` is an HNN extension of `G_M` along the infinite cyclic
   subgroup `<y>`. It is finitely presented and has a finite `K(H_M,1)` of
   dimension at most 3. `G_M` embeds in `H_M`.
2. **Pattern completeness.** For every finite alphabet `A` and every r.e.
   language `L ⊆ A*` there are a word `omega_L(X, Z)` in the generators of
   `H_M` and two letters `X, Z`, and free-monoid homomorphisms
   `phi, psi : A* -> F(gens H_M)`, with `phi` and `psi` depending only on `A`
   and `M`, such that for every `v in A*`

       v in L   <=>   omega_L(phi(v), psi(v)) = 1 in H_M.

   `psi(a) = s^k` for every letter and `phi(a)` is a fixed word of length
   `O(k)`, with the constant depending only on `M` (`k = ceil(log2 |A|)`, at
   least 1). So the reduction has
   linear size and runs in linear time. Only the fixed words `omega_L` depend
   on `L`.
3. **Word problems.** In particular the word problem of every finitely
   generated recursively presented group `G` (a language over its generators
   and their inverses) pattern-reduces to the word problem of `H_M`. Here
   `phi(a^-1)` is in general NOT `phi(a)^-1`.
4. **Lemma E (the upper end of the window).** A substitution
   `phi : (S ∪ S^-1)* -> F(T)` that respects inverses, with `v = 1` in `G` iff
   `phi(v) = 1` in `H`, is exactly an injective homomorphism `G -> H`, and
   every injective homomorphism arises this way.

**Consequence for Zaremsky Problem 1.1 (a class-killing obstruction).** Take
any reducibility `<=_R` between languages that contains the pattern
reductions: for instance linear-time and linear-size many-one reductions,
polynomial-time reductions, or log-space reductions. An `R`-obstruction would
exhibit a group `G` whose word problem is `<=_R` the word problem of no group
of type `F_{n+1}`, and conclude, from "`G <= H` implies `WP(G) <=_R WP(H)`",
that `G` has no type `F_{n+1}` host. No finitely generated recursively
presented `G` has that property: `WP(G) <=_R WP(H_M)`, with `H_M` of type `F`,
for all `n` at once. A group that is not recursively presented embeds in no
finitely presented group, so r.e.-ness already excludes it. This kills
word-problem obstructions through every reducibility that contains the pattern
reductions, including the "time complexity of the reduction" refinement that
the previous lane proposed. By Lemma E, the finest natural reducibility, inverse-respecting
substitution, turns "`WP(G) <= WP(H)` for some `H` of type `F_{n+1}`" into
Problem 1.1 itself. A word-problem-reducibility obstruction must therefore
live strictly between these two ends, or couple the reduction with a
quantitative invariant of the host.

What this does not address: invariants of the host itself (Dehn function,
isoperimetric spectrum, `L^2` invariants), which are not reductions. The Dehn
function is not monotone under embeddings (Birget--Ol'shanskii--Rips--Sapir),
so it needs its own monotonicity device.

Proof: route `type-f-group-receives-re-languages-by-pattern-reductions-proof`.
The Horner identity and the letter-for-letter pattern form are also checked on
3000 random instances by
`experiments/boone-pattern-reductions-2026-09-17/check_pattern_words.py`.
