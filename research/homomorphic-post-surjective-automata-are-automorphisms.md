---
rg: 2
id: homomorphic-post-surjective-automata-are-automorphisms
kind: claim
title: Post-surjective homomorphic automata over any finite group alphabet are automorphisms once the modular group algebras at its abelian composition primes are stably finite
distinct_from:
  homomorphic-group-alphabet-ca-reduce-to-stable-finiteness: that is the injective-implies-surjective direction for homomorphic automata; this is the dual direction (post-surjective implies pre-injective, indeed bijective), with a different mechanism (onto-ness of finitely supported configurations, Grün's lemma and a factor-site count instead of the socle filtration of an injective map).
  linear-proper-domain-duality-is-stable-finiteness: that settles the linear sector over a finite field F_q^k on proper linear subshifts; this covers homomorphic automata over every finite group alphabet, including nonabelian ones where it is unconditional, and affine covers from arbitrary closed domains.
  linear-strict-pairs-are-transposes-of-post-surjective-automata: that matches linear strict automata with linear post-surjective non-pre-injective ones by transposition over a field; this proves that no homomorphic post-surjective non-pre-injective automaton exists under stable finiteness, over any finite group alphabet.
  every-group-is-dual-surjunctive: that is the full dual conjecture for arbitrary automata; this is its homomorphic and affine sector.
artifacts:
  - research/artifacts/homomorphic-post-surjective-automata-2026-09-19.md
---

**ESTABLISHED** by [[homomorphic-post-surjective-automorphism-proof]]. Elementary and self-contained. The only
input is Lemma 1 of the ESTABLISHED `homomorphic-group-alphabet-ca-reduce-to-stable-finiteness` artifact.

**Setting.** `G` is any group, `V` a finite group, and `V[G]` the finitely supported configurations. A
*homomorphic* automaton `L : V^G -> V^G` is a cellular automaton that is a group homomorphism for the pointwise
product. `P(V)` is the set of primes `p` with `Z/p` a composition factor of `V`. Post-surjective and pre-injective
are as in `linear-strict-pairs-are-transposes-of-post-surjective-automata`.

**Theorem.** Suppose `M_n(F_p[G])` is directly finite for every `p ∈ P(V)` and every `n` with `p^n <= |V|`.
1. **Automorphism.** A homomorphic `L` is post-surjective iff `L(V[G]) = V[G]`. Every such `L` is bijective, so it
   is an automorphism of `V^G` whose inverse is a homomorphic automaton, and in particular it is pre-injective.
2. **Unconditional case.** If `V` has no abelian composition factor, the hypothesis is vacuous. Then over every
   group `G`, every post-surjective homomorphic automaton on `V^G` permutes the indecomposable factor sites up to
   isomorphism, and is an automorphism.
3. **Equivalence.** For every `G` the following are equivalent:
   - every post-surjective homomorphic automaton over every finite group alphabet is pre-injective;
   - the same for `F_p`-linear automata on `(F_p^n)^G`;
   - `F_p[G]` is stably finite for every prime `p`.
   With part 3 of `homomorphic-group-alphabet-ca-reduce-to-stable-finiteness`, the homomorphic sectors of
   Gottschalk and of Capobianco–Kari–Taati dual surjunctivity therefore hold at exactly the same groups.
4. **Affine covers.** Give an alphabet `A` a group structure `V`, and let `F(x) = L(x) c` with `L` homomorphic and
   `c` constant. These are exactly the equivariant heap morphisms. Let `X ⊆ V^G` be any closed set with a point
   `x_0` at which `F|_X` has lifts inside `X` for every finite modification of `F(x_0)`. Then `X = V^G` and `F` is
   bijective.

**Why it matters (class kill in the Gottschalk cone).**
- **Invariant.** A group structure on the alphabet making the decoder, or cover, a heap morphism.
- **Dying step.** Lifts at one point give `L` onto `V[G]`, which makes `L` bijective, which makes the domain dense.
- **Consequences.**
  - Under stable finiteness, and at every group for alphabets without abelian composition factors, the following
    cannot be affine for any group structure on the alphabet:
    - counterexamples to `every-group-is-dual-surjunctive`;
    - covers refuting `constant-point-sft-domains-admit-no-post-surjective-covers`;
    - post-surjective decoders of strict pairs, as sought by `strict-pairs-admit-post-surjective-decoders`.
  - The affine sector of CP is exactly stable finiteness of the `F_q[G]`. The converse is the linear counterexample
    recorded in that claim.

**Scope.**
- No group is proved surjunctive or dual surjunctive.
- Rules that are homomorphic only on a sub-alphabet or a subshift are not covered, nor are nonlinear rules.
- No novelty is claimed for the abelian/linear steps. The new content is the nonabelian part and item 4.
