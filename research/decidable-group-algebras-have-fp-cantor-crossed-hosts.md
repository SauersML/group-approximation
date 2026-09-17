---
rg: 2
id: decidable-group-algebras-have-fp-cantor-crossed-hosts
kind: claim
title: Every decidable group algebra over F_2 embeds in a finitely presented central simple crossed product LC(X, F_2) ⋊ P over a torsion-free Farrell–Jones group
distinct_from:
  decidable-group-algebras-have-fp-central-simple-hosts: that asks for any finitely presented central simple host B with K_1 and K_2 of B ⊗ L zero; this restricts B to crossed products LC(X, F_2) ⋊ P over torsion-free Farrell–Jones groups, where the K-theory condition is automatic, and asks only for existence.
  free-minimal-z2-sft-is-quantum-rigid: that asks for one finitely presented crossed product of a free minimal Z^2-SFT over some field; this asks for a family of crossed products over F_2, by arbitrary torsion-free Farrell–Jones groups, containing every decidable group algebra.
  decidable-group-ring-has-fp-projective-simple-host: that asks for ring hosts whose projective elementary groups are finitely presented and simple; this asks for algebra hosts of a fixed dynamical shape and says nothing about elementary groups.
artifacts:
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem.
Then there are:
- a torsion-free group `P` satisfying the `K`-theoretic Farrell–Jones conjecture
  with additive categories as coefficients, with respect to `VCyc`;
- a nonempty compact totally disconnected Hausdorff `P`-space `X`,

such that `B = LC(X, F_2) ⋊ P` is finitely presented as an `F_2`-algebra, is
simple, has centre `F_2`, and admits a unital embedding `F_2[G] -> B`.

**Why it matters.** With `cantor-crossed-product-leavitt-tensors-are-k-trivial`
it gives `decidable-group-algebras-have-fp-central-simple-hosts` (route
`fp-central-simple-hosts-via-cantor-crossed-products`), and hence
`boone-higman-conjecture` through `boone-higman-via-central-simple-leavitt-tensor-host`.
So, granted that chain (which rests on
`leavitt-tensor-hosts-acyclic-steinberg-and-fp`, conditional on the imported
criteria of Khanh arXiv:2609.08428v1), it is at least as hard as Boone–Higman.

**Necessary shape** (artifact Section 6, proved there).
- If `B` is finitely generated, then `P` is finitely generated and `X` is
  conjugate to a `P`-subshift.
- If `P` is infinite and `B` is simple, the action is minimal and `X` is
  infinite.
- A minimal topologically free action gives `Z(B) = F_2`.
- No single pair `(P, X)` serves every `G`. Its host `B` would make
  `(B ⊗ L)^x` one finitely presented simple group containing every such `G`
  (by the route into the target and `boone-higman-via-central-simple-leavitt-tensor-host`),
  and `complexity-bounded-host-classes-are-not-universal` forbids that.

## Attempts

1. **`P = Z`. Dies.** Simplicity forces an infinite minimal subshift, and
   `minimal-subshift-crossed-product-is-not-finitely-presented` says its crossed
   product is not finitely presented.
2. **`P = Z^2`. Gated, and one host at a time.**
   - For abelian `P`, a minimal action in which some `g ≠ e` has a fixed point
     has `g` acting trivially. Then `g` is a non-scalar central element, so a
     host with centre `F_2` needs a free action.
   - Finite presentation forces an SFT (`fp-subshift-crossed-products-are-sfts`,
     unreviewed) and is equivalent to quantum rigidity over `F_2`
     (`sft-crossed-product-fp-iff-quantum-rigid`, unreviewed).
   - Existence of even one such free minimal SFT is the `F_2` form of the open
     `free-minimal-z2-sft-is-quantum-rigid`.
   - Every such host has a faithful Følner rank model
     (`free-minimal-crossed-products-are-simple-with-rank-models`, unreviewed).
     So the `Z^d` case would make every finitely generated group with solvable
     word problem `F_2`-linear sofic, tying it to an open approximation problem.
3. **Amenable `P`. Gated by linear soficity.** Every minimal action of a
   countable amenable group has a faithful Følner rank model over every field
   (`amenable-minimal-crossed-products-have-faithful-rank-models`, ESTABLISHED,
   unreviewed; freeness is not used). A simple host is minimal, so the amenable
   case would make every finitely generated group with solvable word problem
   `F_2`-linear sofic.
4. **`P = F_d`, any `X`. The whole family dies (2026-09-17).**
   - `boundary-crossed-product-is-a-leavitt-path-algebra` gives one finitely
     presented simple host with centre `F_2` over the minimal, topologically
     free SFT `∂F_d`. So nothing dynamical excludes free groups.
   - `free-group-cantor-crossed-products-are-not-universal-hosts` (ESTABLISHED,
     unreviewed) shows some two-generated decidable `H` has `F_2[H]` in no
     finitely presented `LC(X, F_2) ⋊ F_d`, for any `d >= 0` and any `X`,
     simple or not. Finite presentation forces an SFT over any group
     (`fp-crossed-products-force-sft-over-any-group`). Tree SFTs have the local
     extension property, so their ball languages are decidable by local checks.
     So every unit subgroup has doubly exponential word problem
     (`free-group-sft-host-units-have-doubly-exponential-wp`), and
     `complexity-bounded-host-classes-are-not-universal` finishes.
   - Invariant: the local extension property of tree SFTs. Failing step: the
     unital embedding of the hard input `H`. This also covers `P = Z` and
     `P = 1`, independently of Attempt 1.
5. **Hosts from the Boone–Higman embeddings of hyperbolic groups
   (Belk–Bleak–Matucci–Zaremsky, arXiv:2309.06224). Out of scope.** Their natural
   algebras are Steinberg algebras of ample groupoids that are not
   transformation groupoids of torsion-free groups. The Farrell–Jones argument
   does not apply to them.
6. **Sharpened necessary shape (2026-09-17).** Any witnessing family uses:
   - `P` finitely presented
     (`fp-crossed-products-force-finitely-presented-acting-group`, unreviewed);
   - `X` an SFT;
   - `P` not free.

   Open prerequisite, which can fail on its own: the hosts must have no common
   recursive word-problem bound on unit subgroups. The table algorithm of the
   free case works over any `P` with solvable word problem once the SFTs have a
   language algorithm, so a uniform bound on both kills the family as in
   Attempt 4. Therefore a viable `P` must carry minimal,
   topologically free SFTs with finitely presented crossed products whose ball
   languages have no uniform recursive time bound (artifact
   `fp-crossed-product-shape-free-group-kill-2026-09-17`, Section 7, sketch).
