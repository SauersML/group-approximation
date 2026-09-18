---
rg: 2
id: regular-germ-extension-attractors-are-undistorted
kind: claim
title: In finite germ extensions of V, wandering singularities and (in the central-germ regime) attracting points force undistorted cyclic subgroups
distinct_from:
  normal-germ-extensions-of-thompson-v-contain-no-sl3z: that excludes finite-index subgroups of SL_3(Z) through a fixed point on the germ complex and shows BS(1,2) cannot map into the germ groups with a of infinite order; this bounds distortion of elements of the whole group G, which is what BS(1,2) <= GL_2(Q) needs, and leaves n = 2 open only for one explicit dynamical type.
  orbit-preserving-germ-corollary-extensions-of-v-are-rational: that proves rationality and a word-problem bound under hypotheses (H2), (H3), (T); this uses the same regime ((H2) weakened to eventual periodicity) to build two length functions and bound distortion.
  aff-q-does-not-embed-in-aut-thompson-f: that excludes Aff(Q) from T-bar and Aut(F) by where Q must sit; this is a distortion statement about arbitrary finite germ extensions of V.
  regular-germ-extensions-have-no-bs-relations: that is the open statement that the whole regime omits BS(1,k); this is the established part, which reduces it to one dynamical type.
---

**ESTABLISHED** by `regular-germ-extension-attractors-are-undistorted-proof`
(lane-proved, not independently reviewed; elementary, no novelty claimed for the
two length functions themselves).

## Setting

`C = {0,1}^N`, `μ` the uniform Bernoulli measure, `V` Thompson's group acting by
prefix replacements. `G <= Homeo(C)` is a **finite germ extension of `V`** in the
sense of Belk–Hyde–Matucci, arXiv:2407.03149v1, §1 (definitions quoted in
`orbit-preserving-germ-corollary-extensions-of-v-are-rational`): every element has
finitely many singular points, and `V` is exactly the set of elements with none.
`sing(G)` is the union of all `sing(g)`; `(G)_p` is the group of germs at `p` of
elements fixing `p`, and `(V)_p <= (G)_p` the germs of elements of `V`.

For `x ∉ sing(h)`, `h` acts near `x` as a prefix replacement `c z -> d z`; put
`δ_x(h) = |d| - |c|` (the depth gain) and `Lip(h) = sup_{x ∉ sing(h)} |δ_x(h)|`.
Let `s(h) = |sing(h)|`.

Call `G` **regular** if for every `p ∈ sing(G)`:
- **(E)** `p` is eventually periodic (implied by (H2), `Fix_V({p})` finitely
  generated: fact 1 of `orbit-preserving-germ-corollary-extensions-of-v-are-rational`);
- **(H3)** `|(G)_p : (V)_p| < ∞`, or `(V)_p` is normal in `(G)_p`;
- **(T)** `g(p) ∈ V·p` for every `g ∈ G`.

These are the hypotheses of the rationality theorem cited above, which are the
Belk–Hyde–Matucci Corollary 2.10 regime with (H2) weakened to (E).

## Statement

1. **(Any finite germ extension.)** `s` is a length function:
   `s(gh) <= s(g) + s(h)` and `s(g^-1) = s(g)`.
2. **(Regular.)** `Lip(g) < ∞` for every `g ∈ G`, and `Lip` is a length function.
3. **Wandering singularities (any finite germ extension).** Let `a ∈ G` and let
   `O` be an infinite `a`-orbit meeting `sing(a)`, with first and last singular
   points `s_i, s_j` (`s_m = a^m(s_0)`). If the germ of `a^(j-i+1)` at `s_i` (the
   **total germ** of `a` along `O`) is not the germ of an element of `V`, then
   `s(a^n) >= n - (j - i)` for all `n`.
4. **Attractors (regular).** If `a` has an attracting or a repelling periodic point,
   then `Lip(a^n) >= c n - C` for some `c > 0`, `C`, and all `n >= 0`.
5. **Consequences.** In the situation of 3 (any `G`) or of 4 (regular `G`):
   - `<a>` is undistorted in every finitely generated subgroup of `G` containing `a`;
   - `t a t^-1 ≠ a^k` for every `t ∈ G` and every integer `k` with `|k| >= 2`;
   - `a` is not the commutator `[x, y]` of elements generating a Heisenberg group
     `H_3(Z) <= G` with centre `<a>`.

**Corollary (n = 2 and the stepping stones).** Let `G` be a finite germ extension of
`V`, and `D <= G` the image of the divisible unipotent line under an embedding of
`Aff(Q)`, `SL_2(Q)`, `GL_2(Q)` or `U_3(Q)` (for `U_3(Q)`, its centre). Every
nontrivial `a ∈ D` is conjugate to `a^2` (`Aff(Q)`, `GL_2(Q)`: by `x -> 2x`), to
`a^4` (`SL_2(Q)`: by `diag(2, 1/2)`), or is the commutator of a Heisenberg pair
(`U_3(Q)`: `e_13(q) = [e_12(1), e_23(q)]`). So every nontrivial `a ∈ D`:
- has trivial total germ along every infinite `a`-orbit meeting `sing(a)`;
- has, if `G` is regular, no attracting and no repelling periodic point.

## Scope and what is left

- **VA.** `VA` is regular: its singular points end in `0̄` or `1̄` (E); its germs
  commute with the local dilation `L_p`, so `(V)_p` is central in `(VA)_p` (H3); and
  its elements are order-preserving near singular points, so they map the
  minimum (maximum) of a clopen set to another one (T). For `VA` the Corollary is
  subsumed by Burillo–Felipe (root obstruction O4), whose extra ingredient is the
  order structure near singular points.
- **Arbitrary finite germ extensions are no obstruction by themselves.** By
  `shell-cantor-embeddings-are-finite-germ-extensions`, every countably infinite
  group, in particular `BS(1,2)`, and `GL_2(Q)` inside a 2-generated group
  (Higman–Neumann–Neumann), embeds faithfully in a finitely generated finite germ
  extension `E_nu` of `V`. Shell germ groups violate (H3) for non-virtually-cyclic
  inputs (`shell-prefix-core-detects-finite-ray-enumerations`). So the question for
  family A is finite presentation, and a distortion obstruction needs a regime such
  as (E)+(H3)+(T).
- **The remaining type.** In a regular `G`, an element `a` that is conjugate to a
  proper power must have trivial total germs on wandering singular orbits, no
  attracting or repelling periodic points, and at every singular point of a finite
  orbit a germ `α` of `a^q` in the centralizer of a contracting germ `σ_p`. Such germs
  exist with `Lip(α^n) = 0` for all `n` and infinite order: skew products over an
  element of `V` acting on a fundamental annulus, with a level cocycle balancing the
  measure. Neither 3 nor 4 applies to them. That case is the open part of
  `regular-germ-extensions-have-no-bs-relations`.
