---
rg: 2
id: tracial-non-ru-coset-system-with-nonabelian-fibre-exists
kind: claim
title: Some coset constraint system over finite groups with a nonabelian fibre image is tracial but not R^U
artifacts:
  - research/artifacts/ex-kac-quantum-bijection-2026-09-13.md
distinct_from:
  perfect-completeness-isomorphism-compiler: that asks for a machine-indexed family of graph pairs with finite-dimensional completeness on halting inputs; this asks for one coset system with a tracial state and no R^U model.
  mipstar-bcs-tracial-nonru-exists: that is a general Boolean constraint system with the gap, whose trace no symmetry selects; this asks for the gap in coset syntax, where the algebra is a bigalois torsor algebra with an invariant trace and a genuinely quantum symmetry.
  lcs-tracial-ru-gap-equiv-nonhyperlinear: that is the elementary abelian case (binary linear systems), equivalent to a finitely presented nonhyperlinear group; this allows nonabelian fibre groups, where no such equivalence is known.
---

**OPEN.**  Find a coset system `S` over finite groups (definitions in
`coset-systems-are-torsor-isomorphism-games`) with:

- a tracial state on `A(S)`;
- no unital *-homomorphism `A(S) -> R^U`;
- some fibre image `L_q` nonabelian.

By `non-group-dual-colored-qc-qa-pair-from-coset-system` this gives colored
digraphs that are qc- but not qa-isomorphic, whose quantum symmetry is not a
group dual.  As for every colored isomorphism algebra, C*-satisfiability
already implies traciality.

**Caveat.**  A nonhyperlinear group gives this trivially, by adjoining an
unconstrained `S_3` fibre to a linear-system gap.  The instances of interest are
those whose gap is not inherited from an embedded linear system.

## Attempts

- **Independent-set sources (Lin, arXiv:2510.07162, Theorem 6.15 and the
  paragraph after it; MSSV, arXiv:2505.05253, Theorem 3.1).**
  - The sources are Lin's synchronous games `G` with `omega^co = 1` and
    `omega^* <= 1/2`, and their independent-set games on `X(G)`.
  - By `independent-set-injection-splits-as-question-bijection`, completing
    the injection is the same problem as a square presentation of `G`.
  - A torsor presentation is exactly a tracial coset refinement of `G`.
  - Where it dies: by `coset-refinement-forces-rectangular-central-splitting`
    the refining trace must split every pair algebra centrally into accepted
    rectangles.  Lin's perfect commuting strategies arise from a compression
    limit and are not explicit, so the condition cannot be checked.
- **Three-colouring presentations.**
  - (RCS) forces commuting PVMs on adjacent vertices (Corollary 2 of the
    firewall).
  - Where it dies: any source whose perfect models need noncommuting adjacent
    measurements.
- **Context-form presentations with unpadded elementary abelian groups.**
  - This is affine safety (`locally-affine-support-bcs-is-exactly-the-lcs-boundary`),
    which is goal-equivalent.
  - For the unchanged JNVWY verifier it is excluded by
    `jnvwy-active-output-has-no-affine-safe-perfect-model`.
- **Context-form presentations with padding and nonabelian groups.**
  - Edges that say "agree on shared variables" pass (RCS) automatically
    (Corollary 3).  So the remaining step is to lift each Boolean variable
    `x_v` to an `L_v`-valued PVM `ell_v` with `theta_v(ell_v) = x_v`,
    commuting within contexts, with joint spectra in subgroups `T_c` and
    `theta(T_c) ⊆ Allowed_c`.
  - Where it dies: by `exact-label-coset-refinements-are-affine`, suppose
    every edge shares one variable and the blocks of each coset are exactly
    the fibres of the shared bit.  Then the refined trace only reaches
    affine allowed sets, which is the linear-system endpoint, whatever the
    groups and the padding.  Own-variable lifts (`ell_v = sigma_v(x_v)`) are
    a special case.
  - Hidden shared labels are constrained too.  By
    `hidden-labels-import-cross-context-commutation`, any refinement makes
    each non-rectangular context split so that its variables commute with
    the far neighbours.
    - For a synchronous source with NAND pair contexts: on each forbidden
      pair, `P_q^a` commutes with `P_(q')` on a piece `m`, and `P_(q')^(a')`
      commutes with `P_q` on `1 - m`.
    - A factor model with the relevant commutators nonzero admits no
      refinement.
  - What survives: perfect traces whose three-context algebras have enough
    centre for these splittings, and multi-variable edges with nonabelian
    exact label groups.  Whether Lin's games have such traces is not known.
- **Gadgets and completions inside the port algebra (lane
  ex-kac-quantum-compiler).**
  - By `torsor-cfi-port-profiles-are-cosets`, scalar port profiles of torsor
    CFI gadgets are cosets, and affine on Boolean ports, at the `q`, `qa` and
    `qc` levels.
  - By `port-generated-square-completions-force-coset-support`, a closure-safe
    squarification from the verifier's own port projections forces regular
    groups and coset-hull safety.
  - Where it dies: atom-by-atom compilation meets the affine firewall.
  - Not excluded: padding outside the port algebra, which is the regime of
    `coset-refinement-forces-rectangular-central-splitting`, and non-scalar
    ports.
- **Classical index padding.**
  - Every set of classical solutions is the coarse-graining of the coset
    system "all indices equal".
  - Where it dies: that system's algebra is commutative, so it carries only
    classical traces and no gap.
