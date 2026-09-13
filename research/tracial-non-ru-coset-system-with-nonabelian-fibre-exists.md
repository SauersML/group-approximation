---
rg: 2
id: tracial-non-ru-coset-system-with-nonabelian-fibre-exists
kind: claim
title: Some coset constraint system over finite groups with a nonabelian fibre image is tracial but not R^U
distinct_from:
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
  - Where it dies, for own-variable lifts (one group element per Boolean
    value, `ell_v = sigma_v(x_v)`): suppose three points `u, v, w` of a
    context support are "between", i.e. in every coordinate
    `v_i in {u_i, w_i}`, and `v_i = u_i` whenever `u_i = w_i`.
    - Then `sigma(u) sigma(v)^(-1) sigma(w) = sigma(u ⊕ v ⊕ w)`
      coordinatewise, in any group.
    - So `u ⊕ v ⊕ w` must be allowed.
    - Example: the full support of NAND on two variables forces `11`.
  - Lifts that carry information beyond `x_v` must commute with every context
    containing `v`.  No construction of such lifts is known, and no firewall
    excludes them.
- **Classical index padding.**
  - Every set of classical solutions is the coarse-graining of the coset
    system "all indices equal".
  - Where it dies: that system's algebra is commutative, so it carries only
    classical traces and no gap.
