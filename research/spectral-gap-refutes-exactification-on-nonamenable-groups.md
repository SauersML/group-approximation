---
rg: 2
id: spectral-gap-refutes-exactification-on-nonamenable-groups
kind: claim
title: On every nonamenable group, Bernoulli shifts of different entropy never both have approximate right inverses, so no category argument over i.i.d. partitions or factor joinings yields a collapse
distinct_from:
  ornstein-weiss-map-has-no-approximate-right-inverses: that proves the spectral obstruction on groups containing a free subgroup, through its cosets; this runs it along Bowen's measurable free subrelation, on every nonamenable group.
  iid-generators-not-dense-at-positive-rokhlin-supremum: that obstructs density at positive supremum through Rokhlin entropy; this obstructs it at every supremum through a spectral gap.
  bernoulli-isomorphism-from-approximate-right-inverses: that proves approximate right inverses in two shifts would give an isomorphism; this proves they never hold for two different entropies on a nonamenable group.
---

**ESTABLISHED (unreviewed)** by [[spectral-gap-refutes-exactification-on-nonamenable-groups-proof]].

**Setting.** `G` is countably infinite and nonamenable. ARI, DENSE, `d` and `Ind_λ` are as in
`bernoulli-isomorphism-from-approximate-right-inverses` and `iid-density-iff-collapse-and-endomorphism-density`.

1. **Ornstein–Weiss along a free subrelation.**
   - Let `(R, ρ)` be a nontrivial finite base and `U = (R^G, ρ^G)`. Let `F_2 = ⟨a, b⟩` act essentially freely on `U`
     with orbits inside `G`-orbits (`bernoulli-shifts-are-von-neumann-day`), with `T_s(u) = c_s(u)·u`.
   - On sites put `τ^u_s(g) = g·c_s(g^-1 u)^-1`.
   - On the Bernoulli shift `X` with base `R × {0,1}²`, write points as `(u, y, w)`, and put
     `δ_u(y)_g = (y_g + y_(τ^u_a g), y_g + y_(τ^u_b g))`.

   Then `φ(u, y, w) = (u, δ_u(y))` is a non-invertible endomorphism of `X`.
2. **Spectral bound.** For every equivariant Borel `f: X → {0,1}^G`,
   `µ{f_1 + f_(τ_a 1) ≠ y_1} + µ{f_1 + f_(τ_b 1) ≠ w_1} >= 1 − √3/2`, where `τ = τ^u` uses the `u`-coordinate of
   the point. Consequently some `c > 0`, depending only on the cocycles `c_a, c_b`, has `d(φ ∘ ζ, id) >= c` for every
   `ζ ∈ End_G(X)`. (Correction, 2026-09-13: the first landing claimed the constant `(2 − √3)/4` for every equivariant
   Borel `ζ`. That holds in the coset version `ornstein-weiss-map-has-no-approximate-right-inverses`. Here `φ ∘ ζ`
   reads the subrelation from the `u`-coordinate of `ζ(x)`, so the constant degrades as recorded in the proof.)
3. **Above `log 4`.** If `H(κ) > log 4`, then `X_κ` has no approximate right inverses, and `Aut_G(X_κ)` is not dense
   in `End_G(X_κ)`.
4. **Never two entropies.** If `H(κ) ≠ H(λ)`, then `X_κ` and `X_λ` do not both have ARI.
5. **Partition space.** Generating partitions are not dense in `Ind_λ(X_κ)` when `H(κ) ≠ H(λ)`, or when
   `H(λ) > log 4`.
6. **Joining space.** If `H(κ) ≠ H(λ)`, the factor joinings from `X_λ` to `X_κ` and those from `X_κ` to `X_λ` are not
   each contained in the weak* closure of the other.
7. **Zero supremum.** A group with zero supremum is nonamenable. So on every such group three open claims fail:
   - `iid-generators-dense-at-zero-rokhlin-supremum`;
   - `zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms`;
   - `zero-supremum-endomorphisms-have-approximate-right-inverses`.

   Each of the three holds iff no countable group has zero Rokhlin supremum. That is, iff every countable group has a
   free ergodic action of positive Rokhlin entropy (`every-group-has-positive-rokhlin-entropy-action`).

**Reading.**
- Three routes stay valid as implications, but give nothing toward a collapse: `zero-supremum-collapse-via-dense-iid-generators`,
  `zero-supremum-collapse-via-approximate-right-inverses` and `iid-density-from-collapse-and-endomorphism-density`.
  Each input is equivalent to Seward's positive-entropy question, and under that question the bridge claim
  `zero-rokhlin-supremum-forces-bernoulli-collapse` is vacuous.
- A category proof of collapse would need a Polish space of joinings in which both factor-joining sets are dense
  `G_δ`. By item 6 the common closure fails for every pair of different entropies. Any successful mechanism has to
  avoid producing approximate right inverses.
- The obstruction uses no entropy. A would-be right inverse must invent one bit for each orbit of the free
  subrelation, constant along that orbit's tree. That bit gives an odd, almost invariant vector for `F_2` in a
  multiple of its regular representation.
- Still open: DENSE and ARI for a single shift of entropy at most `log 4`, which have no collapse consequence, and
  mechanisms for the bridge claim that are not category arguments.

**Model tests.**
- Amenable groups fail the hypothesis. Over `Z`, ARI holds by the residual factor theorem (model test of
  `bernoulli-isomorphism-from-approximate-right-inverses`), as it must.
- On groups containing `F_2` this is `ornstein-weiss-map-has-no-approximate-right-inverses`, where the threshold
  `log 4` is attained.
- Tarski monsters contain no free subgroup, so the coset version is silent there. The subrelation version applies.
- On nonamenable groups with positive supremum, Rokhlin entropy already refutes items 3–5 for small entropies (item 5 of
  `bernoulli-isomorphism-from-approximate-right-inverses`). The spectral proof covers every supremum.

**Novelty (bounded).** Not found in this graph or in Sections 1, 9 and 10 of arXiv:1804.05269. Bowen's Section 1 was
read only for the statements imported. No wider search was made.
