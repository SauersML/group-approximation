# Adversarial check: `hyperbolic-groups-undistortedly-embed-in-fp-simple-groups` (bh-refute, 2026-09-18)

Rotation item 4 (031299a26). The claim answers the "(quasi-isometrically?)" part of Zaremsky's question,
arXiv:2201.00711 l.495–497, for hyperbolic groups.

Verdict: **PASS**. I re-derived the route and both lemmas. The BBMZ imports (`thrm:hyp_to_contracting`,
`thrm:fin_pres`, `prop:contr_to_simple`) were taken as quoted.

## Lemma `full-group-label-length-bounds-distortion`

- `λ(k)` is the minimum over finite labelled covers of the maximum label length.
  - It is subadditive: refine the covers along `k'^{-1}(U_i) ∩ W_j`.
  - It is inverse-invariant.
  - It is finite on `[[L|X]]` by compactness.
- **Upper bound.** `λ <= A|k|_K`.
- **Lower bound.** For `k ∈ L`, `k^{-1} l_i` fixes the nonempty open set `U_i` pointwise, so local determination
  gives `π(l_i) = π(k)` and `λ(k) >= |π(k)|`.
- **Twisted BT form: local determination.** Suppose `((v_s), γ)` fixes a basic open `U` and `γ^{-1}s = a ≠ s`.
  Perturb `x_s` inside `U_s`. Then `(l·x')_s = v_s(x_a) = x_s ≠ x'_s`, which is a contradiction. So `γ` fixes `S`
  pointwise, and `γ = 1` by faithfulness. Correct.
- The case `K = SV_Γ` is Belk–Zaremsky Thm 2, and the node credits it.

## Lemma `g-free-z-acts-locally-faithfully-on-horofunction-boundary`

- **Step 1.** Cone shadows are cofinal in the basis of atom shadows, because `t`-edges are bridges.
- **Step 3.** This is the key step. Split on whether `w` fixes a vertex `p` of the Bass–Serre tree or is
  loxodromic.
  - Choose a deep edge `e` inside `H(e_u)`, pointing away from `p` (resp. from the axis), far out.
  - Then `we` points away at the same distance.
  - `we ≠ e` because edge stabilizers are trivial.
  - Equal-distance outward edges that are distinct have disjoint half-trees.
  - Degree `2|G| >= 4` leaves room to choose a branch away from the axis inside `H(e_u)`.
- **Step 4.** `w∂C(v) = ∂C(wv)`, and disjoint atoms have disjoint shadows.
- **Correct.**

## Route

1. `G ≤ G*Z` is undistorted, via the retraction killing `t`.
2. `G*Z ≤ Γ = [[G*Z | ∂_h]]` is undistorted, by the plain form. This needs `Γ` finitely generated, which holds
   because it is finitely presented by `thrm:fin_pres`.
3. `Γ ≤ SV_Γ` is undistorted, by the twisted BT form.

Composing gives a QI embedding into the finitely presented simple `SV_Γ`. The `F_∞` refinement is correctly left
OPEN.

## Attacks tried (all failed)

- **Full groups are never locally faithful, since `V` has cone-supported elements.** True, and this is why the
  plain form is applied to `G*Z`, not to `Γ`. The node's calibration makes this point.
- **Torsion `G`, where elliptic `w` could fix open sets.** Excluded by Step 3's fixed-vertex case. Trivial edge
  stabilizers force `we ≠ e`.

## Lesson for general BH

Full-group hosts preserve geometry for free. Suppose an input acts on a compact space so that some label into
it is locally determined (for example, the action is locally faithful). Then it is undistorted in every
finitely generated group between it and its full group, and in `SV_Γ`. So every BBMZ/Belk–Zaremsky-type
Boone–Higman embedding of a locally faithful actor is automatically quasi-isometric. Distortion therefore
cannot obstruct these routes. A host must add distortion only where the input already has it, as `BS(1,2)`
does.
