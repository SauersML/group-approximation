---
rg: 2
id: unbalanced-forward-tables-identify-memory-letters
kind: claim
title: For every design with an unbalanced encoder rule, every minimal forward-sufficient table group identifies two memory addresses
distinct_from:
  strict-automata-live-on-canonical-table-groups: that equates the goal with reverse sufficiency of every minimal table group's reverse table, for all rules; this restricts to unbalanced rules and equates the goal with one coincidence among the memory letters, never looking at reverse products.
  every-injective-ca-has-uniform-single-site-output-law: that is the one-site-law statement over groups; this is its design form, a word problem for the generators of finitely presented table groups.
  unbalanced-effective-rule-certifies-strictness: that is the established certificate, distinct memory letters plus an unbalanced rule give strictness; this is the open universal statement that such letters always collide.
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

**OPEN.** Let `D = (A, S, M, nu, mu)` be a design whose encoder rule `mu` is not balanced, and let
`E` be minimal in `𝓕_D`. Then two of the elements `1`, `x_m` (`m` in `M \ {1_M}`) coincide in `U_E`.

This is equivalent to the goal (Theorem 3 of the artifact), through two routes that form an intended cycle:
- `gottschalk-via-unbalanced-table-memory-collisions`: a strict automaton is amplified to an
  unbalanced injective one, whose design's table group keeps its memory letters distinct;
- `unbalanced-table-memory-collisions-from-gottschalk`: distinct letters make the table group
  non-surjunctive by `unbalanced-effective-rule-certifies-strictness`.

## Attempts

- **Forced cases.** The claim holds in the following cases:
  - **triangular `E`.** The table group is free and every realization is bijective
    (`triangular-forward-tables-force-surjectivity`);
  - **amenable decoder holonomy.** Use `amenable-decoder-memory-forces-surjectivity`;
  - **connected unicyclic `Gamma_E`.** Here it is implied by a positive answer to
    `one-relator-groups-sofic` (`unicyclic-strict-designs-present-nonsofic-one-relator-groups`).
- **Sofic quotients.** Every sofic quotient of `U_E`, the abelianization included, collides memory
  letters in a pattern that balances `mu`. So a design refuting the claim needs a table group whose
  memory letters are separated only by nonsofic structure. For a robustly unbalanced rule this means
  the letters die in every sofic quotient.
- **Binary rules, 2026-09-12 (w3-bal-design).** A refuting binary design needs:
  - **at least four effective memory elements.** With three, the rectangle relation glues two blocks
    through an involution, and an invisible double flip kills injectivity
    (`three-address-binary-injective-rules-are-balanced`);
  - **a non-monotone rule** (`monotone-binary-injective-rules-are-copies`).

  These screens are local: they read only `mu` and coincidences among `M^-1 M M^-1 M`, never the
  decoder.
- **Where a construction must live.** A refuting design needs:
  - a nonsofic memory group, which gives at least two independent cycles in `Gamma_E` unless it is
    a non-sofic one-relator group;
  - a nonamenable decoder holonomy;
  - a decoder identity that uses `x^q = x` at a forward coincidence read by two encoder copies, if
    the host has stably finite prime-field matrix algebras
    (`formal-polynomial-strict-pairs-need-unstable-linearization`,
    `disjoint-footprint-decoders-force-kaplansky-failure`);
  - the rule screens of Section 2 of the artifact.
- **Small memory (w4-bal-census).**
  - **Two symbols, three addresses: holds.** Every forward-sufficient table group of an unbalanced
    design collides two memory letters (`binary-three-address-injective-automata-have-balanced-rules`).
  - **Two symbols, any memory size.** Even when the letters are distinct, a sufficient table group
    must satisfy a relator `x_m^-1 x_m' = x_n^-1 x_n'` with `(m, m') != (n, n')`
    (`binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective`).
