---
rg: 2
id: exact-label-coset-refinements-are-affine
kind: claim
title: A coset refinement of a Boolean context game whose blocks are exactly the shared-variable fibres factors through affine allowed sets, over any groups and with any padding
distinct_from:
  coset-refinement-forces-rectangular-central-splitting: that is a necessary condition on the pair von Neumann algebras of any refined trace; this shows that label-exact refinements of Boolean context games only reach affine allowed sets, so nonabelian local symmetry can escape only through hidden shared labels.
  port-generated-square-completions-force-coset-support: that treats Latin completions inside the port algebra and gets affine safety for two-answer questions; this allows padding by arbitrary finite groups and multi-bit context answers, and gets affine support from label exactness.
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that turns an affine-safe perfect trace into a linear-system gap; this produces such a trace from any label-exact coset refinement.
---

**ESTABLISHED** by `exact-label-coset-refinements-are-affine-proof`.
Reviewed PASS by independent re-derivation (ex-verify2-quantum-l2, part 7
§7.2 and part 8, 0360cef67f).

**Setting.**

- `B` is a Boolean constraint system in context form: variables
  `x_v in Z_2`, and contexts `c` with allowed sets `Allowed_c ⊆ Z_2^c`.
- The context game `G_B` has:
  - questions: the contexts;
  - answers: the allowed assignments;
  - rule: two contexts accept a pair of answers iff they agree on `c ∩ c'`.
- `B` has *single-variable edges* if `|c ∩ c'| <= 1` for all `c != c'`.
- `sh(c)` is the set of variables of `c` that occur in another context.
- A coset refinement `R = (K_c, beta_c, D_(cc'), c_(cc'))` of `G_B` is as in
  `coset-refinement-forces-rectangular-central-splitting`.
- By Goursat's lemma each coset `c_(cc') D_(cc')` is a disjoint union of
  blocks `B_i x B'_i`.  Each block fixes the shared variable, since
  `(beta x beta')(cD) ⊆ Acc`.
- `R` is *label-exact* if, on every edge, distinct blocks carry distinct
  values of the shared variable.  In words: adjacent contexts share no
  information beyond their shared variable.

**Theorem.**  Suppose `B` has single-variable edges and `R` is label-exact.
Then for every context `c` there is an affine subspace
`A_c ⊆ Z_2^(sh(c))` such that:

- **(EL1)** every point of `A_c` is `a|_(sh(c))` for some `a in Allowed_c`;
- **(EL2)** in `A(R)`, the pushed-forward shared variables of `c` agree on
  every edge and commute, and their joint spectrum lies in `A_c`.  This is an
  algebraic identity.
- **(EL3)** Let `B_R` be the Boolean constraint system with contexts `sh(c)`
  and affine allowed sets `A_c`.
  - The pushforward is a unital *-homomorphism `A(G_(B_R)) -> A(R)`.
  - Every perfect `R^U` model of `G_(B_R)` lifts to one of `G_B`.
- **Consequence.**  Suppose `A(R)` has a tracial state and `G_B` has no
  perfect `R^U` model.  Then `G_(B_R)` has a perfect tracial model and no
  perfect `R^U` model, and its allowed sets are affine.
  - This is the linear-system endpoint:
    `locally-affine-support-bcs-is-exactly-the-lcs-boundary` turns it into a
    tracial non-`R^U` binary linear system;
  - `lcs-tracial-ru-gap-equiv-nonhyperlinear` then gives a finitely presented
    nonhyperlinear group.

**What this says.**

- On Boolean context games with single-variable edges, nonabelian fibre
  groups and padding add nothing at exact labels.  The refined trace is
  already affine-safe.
- A torsor completion beyond groups needs *hidden shared labels*:
  - blocks strictly finer than the two fibres of the shared variable;
  - that is, projections in `W*(p_c) ∩ W*(p_(c'))` that are not functions of
    the shared bit;
  - there the label group `K_1/N` can be large and nonabelian, and the shared
    bit an arbitrary function of the label.
- Presentations whose contexts pairwise share at most one variable have
  single-variable edges.  An example is one one-hot context per question plus
  one context per unordered forbidden pair of distinct questions.
- Multi-variable edges allow exact label groups of order up to
  `2^|c ∩ c'|`, possibly nonabelian, and are not covered.

**Model tests.**

- **Elementary abelian `K_c`, blocks given by shared coordinates.**  This is
  the Roberson--Schmidt situation, and the conclusion holds trivially.
- **A nonabelian label-exact refinement.**  `K_c = S_3`, with the shared bit
  given by the sign character on one edge.  The theorem says the shared
  support is the affine set `chi(K^~) + b`.
- **A non-exact refinement.**  `D` is the diagonal of `S_3 x S_3`, with six
  blocks, and the shared bit is the indicator of one transposition, which is
  not affine.  It satisfies the refinement axioms whenever the source
  accepts the corresponding pairs.  The theorem makes no claim there.
