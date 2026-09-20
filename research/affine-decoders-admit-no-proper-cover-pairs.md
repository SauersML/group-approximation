---
rg: 2
id: affine-decoders-admit-no-proper-cover-pairs
kind: claim
title: An affine automaton with lifts at one point of any closed domain forces the full shift exactly when the matrix group rings are directly finite
distinct_from:
  linear-proper-domain-duality-is-stable-finiteness: that needs a linear domain, linear maps and a finite field; this allows an arbitrary closed (nonlinear, non-invariant) domain, affine decoders, finite commutative rings and lifts at a single point, and so kills nonlinear-domain candidates with affine decoders.
  constant-point-sft-domains-admit-no-post-surjective-covers: that is the full nonlinear conjecture; this settles its affine-decoder sector at every surjunctive or modularly stably finite group and locates where the method stops.
  homomorphic-group-alphabet-ca-reduce-to-stable-finiteness: that is injectivity-implies-surjectivity for homomorphic automata on full shifts; this is about post-surjective affine maps from proper closed domains.
  capobianco-kari-taati-dual-surjunctivity-toolkit: that shows linear decoders of one-sided inverses are post-surjective on the full shift; this shows affine post-surjectivity at one point of a proper domain is impossible under direct finiteness.
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided inverse into a strict automaton; this turns it into a proper constant-point SFT cover pair over rings and proves the converse for affine decoders on arbitrary domains.
artifacts:
  - research/artifacts/affine-cover-pairs-direct-finiteness-2026-09-19.md
---

**ESTABLISHED (unreviewed; elementary)** by [[affine-decoders-admit-no-proper-cover-pairs-proof]].

Let `G` be a group, `R` a finite commutative ring and `V = R^k`.

**Theorem.** Suppose `M_k(R[G])` is directly finite. Let `X ⊆ V^G` be any closed set, and let `F = L + b` be an
affine automaton (`L` R-linear). Suppose some `p ∈ X` has a lift in `X ∩ Fin_p` for every finite perturbation of
`F(p)`. Then `X = V^G`, and `F` is an affine automorphism.

**Sharpness.** If `M_k(R[G])` is not directly finite, then a one-sided inverse gives a proper, constant-point,
linear SFT cover pair over `V^G`. So the following are equivalent:
- `M_k(R[G])` is directly finite;
- there is no proper affine one-point cover over `V^G`;
- there is no proper constant-point SFT cover pair over `V^G` with a linear decoder.

**Where direct finiteness holds.** It holds for every `R` and `k` when `G` is surjunctive. It also holds when
`F_p[G]` is stably finite for every `p` dividing `|R|`: nilpotent lifting plus restriction of scalars.

**Class kill (Corollary K).** Take any pair `(X, F)` over a finite alphabet `A` with lifts at one point. Suppose
`F` becomes affine after independent cellwise recodings of the source and the target as `R^k`. Then, at a
surjunctive group, or at a group with stably finite modular group algebras, `X = A^G`.
- So every counterexample to `constant-point-sft-domains-admit-no-post-surjective-covers` (or to CP_col) at a
  sofic group, or at a Kun–Thom wreath, has a decoder that is non-affine under every such recoding.
- Every member of the class dies at the same step: the lifts of the `k` free generators of `V[G]` assemble into a
  finite-memory right inverse. That assembly is the step a nonaffine decoder cannot supply without a local
  section, i.e. without PRUNE.
