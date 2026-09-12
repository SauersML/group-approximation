---
rg: 2
id: formalizable-left-inverse-iff-clean-shear-dilation
kind: claim
title: A binary automaton has a formalizable left inverse exactly when it has a structurally reversible dilation with formally clean ancillas
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that is the open universal statement for every left inverse; this is an exact equivalence for each automaton between formalizability of some left inverse and clean ancillas in a shear circuit.
  injective-binary-automata-have-formalizable-left-inverses: that is the open universal statement for some left inverse; this proves, automaton by automaton, that it is the same as the existence of a clean structurally reversible dilation.
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `tau` be an automaton on `(F_2^n)^G`. The following are equivalent:
- (a) `tau` has a left-inverse automaton `sigma` such that `(tau, sigma)` is formalizable.
- (b) There are `m >= 0` and a structurally reversible word `W` on `(F_2^(n+m))^G`
  (`structurally-reversible-automata-are-formalizable`) such that `W~(X, 0) = (tau~(X), 0)` holds as
  polynomials, for the formal word `W~` and some representative `tau~` of `tau`.

**Functional dilations always exist.** Take `W = P o S o T`, where `T(x,y) = (x, y + tau(x))`,
`S(x,y) = (x + sigma(y), y)` and `P` is the track swap. Then `W(x,0) = (tau(x),0)` as functions, for
every injective `tau`, every left inverse `sigma` and every group. The formal ancilla output is the
defect `X + sigma~(tau~(X))`.

**Consequences.**
- Decomposing `tau` into gates with ancillas never obstructs formalizability and never supplies it.
- A circuit gives a formalizable left inverse exactly when its ancillas vanish formally.
- The input-erasure step is where the defect appears.

Proof: Section 2 of the artifact.
