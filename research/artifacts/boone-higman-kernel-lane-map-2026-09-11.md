# Boone--Higman kernel-lane map and host limits, 2026-09-11

The Boone--Higman conjecture remains open. This record does three things:

1. checks each open hole in the kernel lane against every recorded obstruction;
2. proves that the two newest positive host theorems cannot serve as universal
   hosts;
3. isolates the residually finite case and a necessary complexity consequence
   as measurable targets.

Scope: this lane owns

- the Chatterji--Kassabov maximal-kernel route and the finite bi-index route;
- the fiber-product / conjugacy-finite route;
- the kernel upgrade of Fournier-Facio--Wu--Zaremsky.

The parallel lane owns the germ, shell and twisted Brin--Thompson envelopes
built directly for decidable inputs, the Leavitt/projective ring host, and the
infinite-simple-input form.

## 1. Obstruction check for the kernel-lane holes

### A. `ck-envelope-has-a-finitely-normally-generated-maximal-kernel`

None of the recorded obstructions blocks this hole within its scope:

- `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels` refutes the general
  principle that property (T) gives Max-n. The hole asks for one specially
  chosen maximal kernel of one specific marked cover.
- `ck-quotient-corner-has-infinite-bi-index`, and the refutation of
  `ck-quotient-coset-repair`, concern double cosets of the simple core. This
  route never uses bi-index.
- `ck-cover-quotient-kernel-dichotomy` constrains where a coset-repair
  quotient can live. It says nothing about whether a maximal kernel is finitely
  normally generated.
- The level-ideal screen and the relative elementary equivalence in the
  2026-08-30 literature audit are conditional. They reduce kernels of the form
  E_n(U,I) to finite generation of I. No normal-structure theorem identifies a
  maximal kernel of the finitely presented cover with such a subgroup.
- `abstract-btb-simple-quotient-fp-gate` records the same finite-normal-
  generation step in the abstract twisted setting. There it is the open
  Question 5.9 of arXiv:2603.24687.

Verdict: not blocked, and no mechanism. The property-(T)-free near-solution
`bht-trivial-normal-intersection-envelope` ends at the identical step, so the
Kazhdan hypothesis is not what is missing.

### B. `ck-envelope-simple-core-has-finite-bi-index`

This hole is blocked for the canonical corner, for every nontrivial quotient
and for every marked cover, by `ck-quotient-corner-has-infinite-bi-index`. It
remains open only for different embeddings, and no candidate embedding is
recorded.

### C. `universal-fiber-product-data-for-word-problem-groups`

The general data is not blocked. Its sharp case
`every-wp-group-embeds-in-fp-conjugacy-finite-group`, applied to the input Z,
would produce an infinite finitely presented group with trivial centre and
finitely many conjugacy classes. The node itself records that no such group is
known. The general fiber-product data asks for