---
rg: 2
id: decidable-algebras-embed-in-simple-self-similar-completions
kind: claim
title: Every finitely generated algebra with solvable word problem embeds in the Leavitt--Nekrashevych completion of a free algebra along some matrix recursion whose self-similar quotient is minimal and aperiodic
distinct_from:
  decidable-algebras-embed-in-simple-ln-completions: that asks for a finitely presented base with an injective recursion, which ln-completion-word-problem-reduces-to-base-algebra fences over free bases; this allows a free base and a non-injective recursion, where the base of the completion is the self-similar quotient and no fence is known.
  algebra-boone-higman-conjecture: that is the root; this premise implies it through noninjective-ln-completions-have-self-similar-bases.
---

**OPEN.** Let `K` be a computable field. For every finitely generated `K`-algebra `A` with solvable
word problem there are a free algebra `B = K<g_1..g_m>`, `d >= 2`, and a matrix recursion
`ψ : B -> M_d(B)`, such that, with `J` the self-similar kernel:
- `B/J` is ψ̄-minimal;
- `(B/J, ψ̄)` is aperiodic;
- `A` embeds in `O_ψ(B)`.
Then `O_ψ(B)` is a finitely presented simple envelope of `A`, by
`noninjective-ln-completions-have-self-similar-bases`, part 4.

**Test case.** The monomial benchmark `A_X = K<x,y>/(x y^n x : n ∈ X)`, `X` decidable. Recursions whose
entries are monomials act as partial transducers, and iterating a finite transducer can simulate a
Turing machine. The natural design:
- a closed block `x y^n x` runs a decider for `X` in its own cells, one step per level of the recursion;
- the block dies, meaning every branch becomes undefined, exactly when the decider accepts;
- an input track is kept, so that the checking branch stays injective on surviving words.
The two difficulties are:
- **minimality:** every surviving element must have a descendant that is a nonzero scalar, while
  forbidden words have none. Erasing branches must refuse any word with an unfinished closed block,
  and every closed block, including junk ones, must finish in finite time;
- **aperiodicity:** it has to be checked for non-diagonal recursions.

## Attempts

1. **Reduction to a lossless transducer** (2026-09-18, lane `bh-algebra`). By
   `lossless-monomial-recursions-give-simple-completions`, the benchmark `A_X` embeds in a finitely
   presented simple completion as soon as there is a lossless row-monomial recursion `ψ` on a free
   algebra with a peel state whose *dying words* are exactly the words over `{x, y}` with a factor
   `x y^n x`, `n ∈ X`, and for which every surviving word erases along some branch. So the premise, for
   monomial inputs, reduces to a transducer-design problem.
2. **Substitution dynamics, not a finite automaton** (same lane). A level of `ψ` rewrites each output
   letter again, so from a single word the process runs as a branching substitution (an L-system on `d`
   branches). "Dying at level `N`" can need `N` far larger than the word length. So this is *not* bounded
   by `ln-completion-word-problem-reduces-to-base-algebra`: that node's level bound `N <= 2l` holds only
   for injective `ψ`, where no word dies late. For non-injective `ψ` the time-to-die carries the
   complexity, which is why the fence does not fence this premise.
3. **The crux.** A row-monomial recursion is a *fixed finite* object (finitely many word entries). Its
   dying set is the language killed by iterating one finite substitution with branching. Whether every
   decidable `X` is reachable this way, or only a restricted class (a branching-D0L analogue), is open. A
   proof of the premise for all `X` needs either that reachability, or a base that grows with `X` (still
   free, so that the fence stays inapplicable), or non-lossless recursions where cancellation adds power.
   No obstruction is known: the fence is inapplicable, and the substitution dynamics is Turing-shaped.
4. **Where the K-theory of these hosts lives** (2026-09-18, lane `bh-algebra`, after `bh-free-53`).
   - `binary-self-similar-completions-over-free-bases-have-zero-kh` (d4f9c0796) gives
     `KH(O_ψ(K<X>)) = 0` for binary `ψ`, injective or not.
   - By `noninjective-ln-completions-have-self-similar-bases`, `O_ψ(K<X>) ≅ O_(ψ̄)(B/J)` with `ψ̄`
     injective. So its nil terms, the whole of `K` minus `KH`, are those of an injective completion
     over the self-similar quotient `B/J`.
   - For the lossless monomial recursions of `lossless-monomial-recursions-give-simple-completions`,
     `B/J` is the monomial algebra `K<X>/(dying words)`. So the ring-side `K`-gate for these hosts
     reduces to twisted-nil vanishing over monomial algebras, not over the free base.
   - **The same tension from both sides.** The recursions that escape the complexity fence are the
     non-injective ones. Their `B/J` is a monomial algebra with infinitely many relations when `X` is
     hard, and such algebras are not expected to be coherent. So escaping the fence is exactly what
     endangers regularity.
   - **For the group transfer the alphabet size is irrelevant.** The group route uses `O_ψ ⊗ L_2`, and
     `KH(A ⊗ L_2) = 0` for every `A` (`leavitt-tensor-k-theory-is-pure-twisted-nil`). The
     "keep `d = 2`" caution matters only when `O_ψ` itself is used as the `K`-trivial host.
   - *Lesson for general BH.* Complexity and regularity pull against each other in every self-similar
     host: complexity needs a non-injective recursion, and non-injectivity puts a non-coherent monomial
     algebra under the completion. A universal route needs a coherence mechanism for monomial algebras
     with decidable, non-regular relation sets, or it must get complexity from somewhere other than the
     kernel `J`.
