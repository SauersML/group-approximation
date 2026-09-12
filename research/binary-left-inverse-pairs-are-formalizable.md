---
rg: 2
id: binary-left-inverse-pairs-are-formalizable
kind: claim
title: Every binary cellular automaton pair with a left-inverse identity admits representatives in which the identity is formal
refuted_by: [binary-left-inverse-pairs-need-not-be-formalizable]
distinct_from:
  formal-polynomial-strict-pairs-need-unstable-linearization: that proves formal pairs are bijective under direct finiteness; this asks whether every pair over F_2^n alphabets can be made formal, which would make direct finiteness of F_2[G] enough for surjunctivity over alphabets of size 2^n.
  multilinear-collapse-defect-does-not-obstruct-bijectivity: that shows canonical multilinear representatives can fail to be formal even for a reversible pair; this asks for some representatives, on possibly larger memories, that are formal.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
  - research/artifacts/binary-formalizability-refutation-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**REFUTED** by `binary-left-inverse-pairs-need-not-be-formalizable`, with `G = Z` and `n = 1`.

The statement was: for every group `G` and `n >= 1`, if `tau`, `sigma` are cellular automata on
`(F_2^n)^G` with `sigma o tau = id`, then there are polynomial representatives of their local rules,
on possibly larger memories, with `sigma o tau = id` as a formal polynomial identity.

**Why it matters.** With `formal-polynomial-strict-pairs-need-unstable-linearization`, this claim
makes every group with stably finite `F_2[G]` surjunctive over every alphabet of size `2^n`, through
the route `formalizable-pairs-reduce-surjunctivity-to-kaplansky`. On a host with stably finite
`F_2[G]`, a strict binary pair is never formalizable. So any counterexample there is exactly a
non-formalizable strict pair.

## Attempts

- **Sitewise pairs (memory `{1}`):** true on every group.
  - A shear `x_i -> x_i + f(other coordinates)` is a formal involution in characteristic 2.
  - Shears with `f` the indicator of one point realize the transpositions along hypercube edges.
    These generate `Sym(F_2^n)`, because the hypercube is connected.
  - So every permutation is a composite of shears, and the reverse composite inverts it formally.
    Artifact, Section 6.2.
- **Canonical multilinear representatives:** they can fail
  (`multilinear-collapse-defect-does-not-obstruct-bijectivity`), so the claim needs freedom in the
  representatives.
- **Bennett form:** `V = P o S o T` with `T(x,y) = (x, y + tau(x))`, `S(x,y) = (x + sigma(y), y)` and
  `P` the track swap. `V` is formally invertible with any representatives, and
  `V(x,0) = (tau(x), x + sigma(tau(x)))`. Formalizability asks for representatives in which the
  second coordinate vanishes formally on `X_0 = A^G x 0`. Artifact, Section 6.3.
- **Where it stops.**
  - Replacing `tau` by `tau + (X^2 - X) P` and `sigma` by `sigma + (Y^2 - Y) Q` changes the defect by
    `J_sigma(tau)(X^2 - X) P` plus higher terms, plus `(tau'^2 - tau') Q(tau')`.
  - Cancelling it is an equivariant finite-memory solvability problem inside the ideal
    `(X_h^2 - X_h)`. No argument is known on any group with nontrivial memory, and no
    non-formalizable pair is known.
  - A non-formalizable **bijective** pair on some group would refute this claim without deciding
    Gottschalk.
- **Decomposition (gk-fz-decompose, 2026-09-12).**
  - Words in track shears with arbitrary memories, sitewise `GL_n(F_2)` maps and constant
    translations form formalizable pairs with their reversed words, on every group and after
    regrouping along a finite-index subgroup (`structurally-reversible-automata-are-formalizable`).
    All of them are bijective.
  - With ancillas, functional dilations always exist (two shears and a swap).
    `formalizable-left-inverse-iff-clean-shear-dilation` shows that formally clean ancillas are
    exactly a formalizable left inverse, so circuit decompositions, including Kari-type block
    permutations, only re-express the claim. The input-erasure step carries the defect.
  - Left-inverse extensions over every `F_(2^k)` always exist
    (`binary-left-inverse-pairs-extend-over-every-finite-field`), so the obstruction is uniformity
    of degree.
  - The Kaplansky payoff needs only some left inverse:
    `injective-binary-automata-have-formalizable-left-inverses`, fed from this claim.
- **Refuted (gk-fz-bennett, 2026-09-12, cf99b38215).**
  - **Classification.** Over a bi-orderable group, formalizable one-track pairs are affine
    translations (`formalizable-binary-pairs-over-biorderable-groups-are-affine`). The proof:
    - the formal identity is two-sided, since `F_2[G]` is a domain;
    - the translates of the encoder polynomial are algebraically independent;
    - the extreme variable enters with degree `DE >= 1`, which forces single-cell windows.
  - **Witness.** The six-cell marker involution on `{0,1}^Z` is not affine.
  - **What survives, both still giving the Kaplansky payoff:**
    - stable formalization with identity ancilla tracks (gk-free-neg's
      `injective-binary-automata-are-stably-formalizable`);
    - formal pairs after regrouping along a finite-index subgroup, where several tracks carry shears.
  - **Lemma C** of the refutation artifact: the Bennett defect can always be pushed into `I^2`, so
    the obstruction is never first order.
