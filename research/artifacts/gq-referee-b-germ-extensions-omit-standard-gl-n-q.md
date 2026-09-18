# Referee report (citation/hypothesis lens): `germ-extensions-omit-standard-gl-n-q`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: the claim as landed at 4a58a2b5b.

## Verdict

**PASS, with three wording amendments (W1–W3).** None changes a conclusion.

## Checks

- **Identity principle for each example L. Correct.**
  - Projective frames: `n+1` points in general position.
  - Affine bases over `R` and `Q_p`.
  - Adelic affine: `x_0 + NẐ^n`, then `A = I` on the vectors `N e_i`, then `b = 0`.
- **The group property of piecewise-L homeomorphisms with pieces in Δ, and items 1–3. Correct.**
  - The dense open set `W = D(c) ∩ c^{-1}D(b)`.
  - `D(bc) ⊇ W`.
  - Item 1's dense open `E = ⋃ (U_x ∩ D(b_x))`.
  - Item 3 needs only that the `b_i` have finite piece sets; closure then gives `B ⊆` the pieces-in-`⟨P(b_i)⟩`
    group.
- **Corollary (a) against the source.** Belk–Hyde–Matucci, arXiv:2407.03149v1, read in HTML:
  - The definition of a finite germ extension is in the introduction. Its first condition reads: "Every
    element of G has only finitely many singular points". Here
    `sing(h) = {p ∈ X | h does not agree with any element of B on any neighborhood of p}`.
  - The definition also requires that `B` is exactly the elements with no singular points, and a localization
    condition.
  - The node uses only the first condition, which is weaker. So every BHM finite germ extension satisfies its
    hypothesis.
  - The ambient space in BHM is Hausdorff (Notation 2.2), which matches.
- **Corollary (b). Correct.**
  - The adjoint embedding `PGL_n(K) → GL_{n^2}(K)` has kernel the scalars.
  - Mal'cev's theorem applies, and a divisible subgroup has trivial image in every finite quotient.
- **Corollary (c). Correct.** `v_p(λ^{-1}) >= 0` and `n·v + 1 = 0` are incompatible.
- **Corollary (d). Correct** under the node's own definition (finite piece set, dense `D(h)`).
- **Remark 5.5.** Checked against the survey text: it concerns PIP homeomorphisms of higher-dimensional
  spheres. The node's disclaimer is accurate.
- **The `distinct_from` target** `higman-group-embeds-in-no-piecewise-analytic-circle-group` exists on main.

## Wording amendments

- **W1 (citation locus).** "Notation 2.2" in BHM only fixes the setting: "let X be a Hausdorff space, let
  B≤Homeo(X), and let G be a finite germ extension of B". The definition is in BHM §1. Cite "BHM §1 (definition),
  Notation 2.2 (setting)". Also say that only its condition (1) is used.
- **W2 (towers).** "off a finite set it is locally finite" is true only for two-level towers. For a tower of
  length `k`, argue by induction:
  - off the finite singular set of `g` relative to level `k−1`, the set `S(g)` locally equals `S(h)` for some
    `h` at level `k−1`, which is closed and nowhere dense by induction;
  - so `S(g)` is closed and nowhere dense, because nonempty open sets are infinite in a Hausdorff space without
    isolated points.
- **W3 (adelic example in (b)).** `A_f^n ⋊ GL_n(Q)` is linear over the commutative ring `A_f`, not over a field.
  Mal'cev's theorem still applies to finitely generated linear groups over commutative rings. See the
  self-contained proof in `piecewise-commutative-linear-hosts-miss-linear-gl-n-q-proof`, step 3.
