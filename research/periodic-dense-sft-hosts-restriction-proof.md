---
rg: 2
id: periodic-dense-sft-hosts-restriction-proof
kind: route
title: Full-group elements preserve every closed invariant set, a nontrivial element is seen on a dense invariant union, and finite orbits or one-dimensional folding give tame restrictions
target: periodic-dense-sft-hosts-have-only-thompson-simple-subgroups
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-free-32-order-rigidity.md
---

Lane proof, elementary, not independently reviewed. Notation as in the target.

## Item 1: restriction principle

- *Invariance.* Let `h ∈ [[𝒢]]` and let `Z ⊆ Y` be closed and `𝒢`-invariant. For each `y`, the
  point `h(y)` is the range of a germ in `𝒢` with source `y`, so it lies in the `𝒢`-orbit of `y`.
  Hence `h(Z) ⊆ Z`, and likewise for `h^{-1}`, so `h(Z) = Z`.
- *Restriction is a homomorphism into the full group of `𝒢|_Z`.* Restricting a compact open
  bisection of `𝒢` to `s^{-1}(Z)` gives a compact open bisection of `𝒢|_Z`. So `h ↦ h|_Z` is a
  homomorphism `[[𝒢]] → [[𝒢|_Z]]`.
- *Some piece sees every nontrivial element.* Let `S ≤ [[𝒢]]` be simple and `s ∈ S ∖ {1}`. The
  support `{y : s(y) ≠ y}` is nonempty and open. The union of the `Y_j` is dense, so the support
  meets some `Y_j`, and `s|_{Y_j} ≠ id`.
- *Conclusion.* The kernel of `S → [[𝒢|_{Y_j}]]` is a normal subgroup of `S` not containing `s`,
  so it is trivial. ∎

## Item 2: dense finite orbits

- *The pieces.* For `x ∈ X` with finite orbit `O(x)` of size `k`, put `Y_x = C × O(x)`. It is
  closed and invariant under `G_V × (Λ ⋉ X)`. The union of the `Y_x` is dense in `C × X`, because
  such `x` are dense.
- *Their full groups are copies of `V`.* An element of `[[G_V × (Λ ⋉ O(x))]]` acts on
  `C × O(x) = ⊔_k C` locally by (prefix replacement) × (a point of `O(x)` to a point of `O(x)`).
  So it lies in the Higman--Thompson group `V_{2,k}`. The isotropy of `Λ` at `x` acts trivially on
  points and does not appear. `V_{2,k} ≅ V`, since `V_{2,r} ≅ V_{2,1}` for every `r` (Higman).
- *Conclusion.* By item 1, every finitely generated simple subgroup embeds in `V`. Its word problem
  reduces to that of `V` by rewriting generators.
- *Without `G_V`.* For `[[Λ ⋉ X]]` alone, the restricted groups are subgroups of `Sym(O(x))`, which
  are finite. ∎

## Item 3: dimension one

- *Encoding.* Encode `(c, x) ∈ C × A^Z` by `z_n = (c_n, x_n, x_{-1-n})`, `n ≥ 0`.
- *Generators have ω-regular graphs.* An element of `[[G_V × (Z ⋉ X)]]` is given by a finite
  clopen partition into rectangles `[p] × [u]`, where `u` is a pattern on `[-r, r]`. On each
  rectangle it acts by `(pt, x) ↦ (qt, σ^k x)` with `|k|` bounded.
  - In the folded coordinates both prefix replacement and `σ^k` move letters by a bounded offset.
    For example, `σ` sends `(x_n, x_{-1-n})` to `(x_{n+1}, x_{-n})`.
  - So each graph is a synchronous ω-regular relation. A finite buffer handles the offsets, and
    the cylinder tests read a bounded prefix.
- *The domain is ω-regular.* A sofic `X` is the set of labels of bi-infinite paths in a finite
  labeled graph. In folded form, a nondeterministic safety automaton guesses the two half-paths and
  checks the junction at `0`. By König's lemma, an infinite run exists iff the point is in `X`.
- *Conclusion.* Every finitely generated subgroup acts by parameter-free ω-automatic bijections.
  Step 4 of `definable-parameter-hosts-specialization-proof` puts its word problem in PSPACE. That
  step does not use finite presentation.
- *Periodic points.* A nonempty `Z`-SFT contains a periodic point, from a closed walk in its finite
  graph. So a minimal `Z`-SFT is one finite orbit, and an irreducible `Z`-SFT has dense periodic
  points, so item 2 applies. ∎
