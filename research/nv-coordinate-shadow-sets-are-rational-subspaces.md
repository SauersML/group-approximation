---
rg: 2
id: nv-coordinate-shadow-sets-are-rational-subspaces
kind: claim
title: "In nV a coordinate shadow is bounded exactly when the coordinate offsets are, so the shadow-bounded directions of any Z^d form a saturated subgroup, and over a Z^2 with a hyperbolic twist every shadow set D_J is empty or all of P^1(Q)"
distinct_from:
  coordinate-shadows-rigidify-abelian-normalizers-in-nv: that proves D_J is permuted by twisting matrices and kills finite nonempty D_J; this proves D_J is always the projectivization of a rational subspace. That turns the survivor shape 'empty or infinite' into 'empty or everything', and it kills every infinite proper D_J.
  heisenberg-in-nv-forces-drift-free-central-element: that is a mean-offset (measure) invariant of distorted elements; this is the sup-offset along whole cyclic groups, which is exactly J-shadow boundedness and is additive on commuting elements.
  infinite-order-elements-of-v-have-hyperbolic-periodic-points: its route proves that a bounded cocycle gives finite order in V; this is the coordinatewise nV version and its converse, applied to J-shadows of abelian subgroups.
  brin-thompson-2v-is-not-a-t-menable: that is the negation target; this narrows the shape of any Sol or Burger-pair witness for it.
---

**ESTABLISHED** by `nv-coordinate-shadow-sets-are-rational-subspaces-proof`
(2026-09-19, swarm-0917-w14-w14-nv-pull). The proof is elementary and imports nothing. It has
not been reviewed by a verifier lane.

**Setting.** This is the setting of `coordinate-shadows-rigidify-abelian-normalizers-in-nv`.
- Take `g ∈ nV` with a brick table `(u_1s_1, …, u_ns_n) ↦ (U_1s_1, …, U_ns_n)`.
- The **offset** of `g` in coordinate `i` at `z` is `c_i(g)(z) = |U_i| - |u_i|`, read on the
  brick that contains `z`.
  - Refining a brick appends the same letter to `u_i` and to `U_i`. So `c_i(g)` does not
    depend on the table.
  - It is a cocycle: `c_i(gh)(z) = c_i(g)(hz) + c_i(h)(z)`.
- For `J ⊆ {1..n}`, call `g` **J-offset-bounded** when
  `β_J(g) = sup_{t ∈ Z, z, j ∈ J} |c_j(g^t)(z)| < ∞`.
- The J-shadow `ω_J(g)`, the set `D_J` and J-boundedness are as in that node.

**Theorem.**
- **(T1) Shadows are offsets.** `g` is J-bounded iff `g` is J-offset-bounded. Quantitatively:
  - `β_J(g) <= D·ω_J(g)`;
  - `ω_J(g) <= 2·Π_{j∈J} (D+β+1)·2^{D+2β+1}`, where `β = β_J(g)` and `D` is the largest
    prefix length in a table of `g` or of `g^{-1}`.
  - With `J = {1..n}` and (S3), this gives: **an element of `nV` has finite order iff all its
    coordinate offsets stay bounded along its powers.**
- **(T2) Subgroup.** Let `Z^d = ⟨x_1, …, x_d⟩ ≤ nV`. Then
  `Λ_J = {v ∈ Z^d : x^v is J-bounded}` is a **saturated subgroup** of `Z^d`, and
  `D_J = P(Λ_J ⊗ Q)`. The whole of `Λ_J` is uniformly J-bounded:
  `sup_{v ∈ Λ_J, z} |c_J(x^v)(z)| < ∞`, and `sup_z |pr_J(x^{Λ_J} z)| < ∞`.
- **(T3) Twists.** Suppose `g^{-1}x^vg = x^{Mv}` with `det M ≠ 0`. Then `MΛ_J ⊆ Λ_J`, and
  `MΛ_J = Λ_J` when `M ∈ GL_d(Z)`. For `d = 2`:
  - `D_J` is `∅`, a single rational point, or all of `P^1(Q)`;
  - in the middle case every twisting matrix fixes that rational line, so the normalizer image is
    virtually abelian and has no hyperbolic element. This contains (S5), and in fact shows that a
    finite nonempty `D_J` is always one point.
- **(T4) Logarithmic floor.** If `g` has infinite order, then
  `max_i sup_{0<=s<=t, z} |c_i(g^s)(z)| >= (log_2 t)/(2n) - O_g(log log t)`.
  - The maximum may be taken over the coordinates outside any `J` with `g` J-bounded; the
    constant `2n` then becomes `2(n - |J|)`.

**Forced shape of a survivor (sharpening).** Let `Z^2 ≤ nV` be normalized by an element with a
hyperbolic twist. This covers every Sol lattice and every Burger pair `(Z^2 ⋊ Γ, Z^2)` for
`brin-thompson-2v-is-not-a-t-menable`.
- For every `J`, either **every** nonzero `x^v` is J-bounded or **none** is.
- Let `J_max` be the union of the `J` of the first kind. By `ω_{J∪J'} <= ω_J ω_{J'}`, `J_max`
  is itself of the first kind. It is a proper subset, by (S3).
- On `J_max` the whole `Z^2` has uniformly finite orbit shadows.
- For each `i ∉ J_max`, every nonzero `x^v` has unbounded `i`-offsets.
- Along every ray those offsets grow like `Θ(log t)`:
  - the lower bound is (T4);
  - the upper bound holds because offsets are at most a constant times word length, and the fibre
    `Z^2` of a Sol lattice is exponentially distorted.

**Class killed.** Every Sol or Burger-pair candidate over a `Z^2 ≤ nV` in which some nonzero element is
J-bounded and some other element is not, for some `J`, is killed. The invariant is the J-offset
sup-norm. The step where every member dies is (T3): `Λ_J` would be an invariant rational line of a
hyperbolic matrix.

This contains:
- every `Z^2` with a nonzero element that fixes some coordinate pointwise (for instance a
  stabilized element `h × id`), unless the whole `Z^2` has bounded shadows on that coordinate;
- every `D_J` that is infinite but not all of `P^1(Q)`, the case (S5) left open.

**Untouched.** Two things remain open:
- the case `J_max ≠ ∅` in which every element is bounded on `J_max`;
- the fully mixing case `J_max = ∅`, where every nonzero element has `Θ(log t)` unbounded offsets
  in every coordinate. Reversible-Turing-machine elements, such as those behind Callard–Salo and
  SMART, move letters between coordinates, which makes them the natural candidates here. Their
  offset growth has not been computed.

No `Z^2 ≤ nV` with a hyperbolic twist is known in either case.
