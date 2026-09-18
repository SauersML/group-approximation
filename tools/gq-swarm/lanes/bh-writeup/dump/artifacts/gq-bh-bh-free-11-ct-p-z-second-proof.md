# An independent second proof that the groups CT_P(Z) are pairwise non-isomorphic, for finite P (bh-free-11, 2026-09-18)

This is a cross-check of `ct-p-z-groups-are-pairwise-nonisomorphic` (d7a1aa918), which
answers Kourovka 17.60. I worked it out without seeing that node, which had already
landed while `UNOWNED.md` still listed the problem as open. It uses a different, one-germ
invariant, and it covers finite `P` only.

**How it differs from the node.**
- **The node's route.** It reads each prime axis as an atom among the stable sets of the
  contracting germs. It then labels the axis by the eigenvalues of the neutral subgroup
  acting on a shell quotient.
- **This route.** It uses one germ at a time. The germ `×p` at `0` has as its
  forward-and-backward invariant core the set of directions in which `p` is a unit. The
  germ itself rotates that core isometrically, and the continuous eigenvalues of the
  minimal pieces carry the other primes.

Both proofs rest on the same inputs:
- the parent model `ct-p-z-is-a-one-vertex-k-graph-full-group`;
- Matui's spatial realization, as `iso2` or as `spatial`.

Status: lane proof, not reviewed. No priority claimed.

## The invariant

Let `G` be an ample groupoid: étale, Hausdorff, with totally disconnected unit space.

- **Locally stable isotropy.** Let `γ ∈ G_x^x`, and let `B ∋ γ` be a compact open
  bisection with partial homeomorphism `α = α_B`, so `α(x) = x`. Call `γ` *locally
  stable* if `x` has arbitrarily small compact open neighbourhoods `U ⊆ s(B)` with
  `α(U) ⊆ U`. Representatives agree near `x`, so this does not depend on `B`.
- **Stable core.** For such a `U`, put `K(α, U) = ⋂_{n≥0} α^n(U)`. It is compact, and
  `α(K) = K` because `α` is injective.
- **Eigenvalue primes of one core.** `𝒫(α, U)` is the set of primes `ℓ` such that some
  minimal subset `M` of `(K(α, U), α)` has every `ℓ`-power root of unity among its
  continuous eigenvalues.
- **Eigenvalue primes of `γ`.** If `γ` is locally stable, `𝒫(γ)` is the intersection of
  `𝒫(α_B, U)` over all pairs `(B, U)`, where `B ∋ γ` is a compact open bisection and
  `U ⊆ s(B)` is a compact open neighbourhood of `x` with `α_B(U) ⊆ U`. Otherwise
  `𝒫(γ) = ∅`.
- **The invariant.** `𝓘(G) = ⋃_{x, γ ∈ G_x^x} 𝒫(γ)`.

An étale groupoid isomorphism restricts to a homeomorphism `h` of unit spaces with
`α_{Φ(B)} = h α_B h^{-1}`. It therefore preserves isotropy, local stability, stable
cores, minimal subsystems up to conjugacy, and continuous eigenvalues. So `𝓘` is an
isomorphism invariant.

**Claim.** `𝓘(G_{Λ_P}) = P ∪ {2}` for `P ≠ ∅`, and `𝓘(G_{Λ_∅}) = ∅`.

So `CT_P(Z) ≅ CT_Q(Z)` gives `G_{Λ_P} ≅ G_{Λ_Q}` by Matui, hence equal invariants, hence
`P = Q`.

Notation follows the parent node `ct-p-z-is-a-one-vertex-k-graph-full-group`.

- **The groupoid.** `P' = P ∪ {2}`, and `G = G_{Λ_P}` has unit space `Ẑ = ∏_{q ∈ P'} Z_q`.
- **Basic bisections.** `Z(λ, μ)` acts by the canonical box map
  `κ(y) = r_λ + (m_λ/m_μ)(y − r_μ)` from `B(μ)` to `B(λ)`.
- **Boxes.** `B(r, m) = r + mẐ`, and boxes form a basis of clopen sets.

For a closed subgroup `C` of a compact abelian group, write `Ĉ` for its Pontryagin dual.
A torsion group has *infinite `ℓ`-part* if its `ℓ`-primary component is infinite.

## Step 0. Two facts about rotations

**(R1)** Let `C` be a compact monothetic group with topological generator `g`, and let
`H ≤ C` be closed. Rotation by `g` on `C/H` is minimal and equicontinuous. Its continuous
eigenvalues are exactly `{χ(g) : χ ∈ (C/H)^∧}`, and `χ ↦ χ(g)` is injective.
- Minimality: the orbit of the identity coset is dense.
- Eigenvalues: every continuous eigenfunction of a minimal rotation on a compact abelian
  group is a multiple of a character (standard; Halmos–von Neumann). Injectivity holds
  because `g` generates a dense subgroup.

**(R2)** Let `q` be a prime and `a ∈ Z_q^×` not a root of unity. Then `C = cl⟨a⟩ ≤ Z_q^×`
has infinite `q`-part in `Ĉ`. For every prime `ℓ ≠ q`, the `ℓ`-part of `(Z_q^×)^∧` is
finite.
- **Structure of `Z_q^×`.** For `q` odd, `Z_q^× ≅ μ_{q−1} × (1 + qZ_q)` with
  `1 + qZ_q ≅ Z_q`. For `q = 2`, `Z_2^× ≅ {±1} × (1 + 4Z_2)` with `1 + 4Z_2 ≅ Z_2`.
- **`C` contains `Z_q`.** `C` is infinite, since `a` is not a root of unity. So
  `C ∩ (1 + qZ_q)`, respectively `C ∩ (1 + 4Z_2)`, is an infinite closed subgroup of
  `Z_q`, hence open, hence `≅ Z_q`.
- **Duals.** Dualizing `Z_q ↪ C` gives a surjection `Ĉ ↠ Q_q/Z_q`, so `Ĉ` has infinite
  `q`-part. Also `(Z_q^×)^∧` is `Z/(q−1) × Q_q/Z_q`, respectively `Z/2 × Q_2/Z_2`, whose
  `ℓ`-part is finite for `ℓ ≠ q`.

Two consequences:
- a subgroup of `S^1` with infinite `ℓ`-part contains every `ℓ`-power root of unity,
  because every infinite subgroup of `μ_{ℓ^∞}` is `μ_{ℓ^∞}`;
- the `ℓ`-part of a quotient of a torsion abelian group `A` is the image of the `ℓ`-part
  of `A`.

## Step 1. Isotropy germs are affine

Let `γ ∈ G_x^x`. It lies in some basic bisection `Z(λ, μ)`, with `λz = μz = x`, and there
`α = κ` with `κ(x) = x`.
- **The germ.** Near `x`, every representative of `γ` equals
  `κ(y) = x + a(y − x)`, `a = m_λ/m_μ`, a positive `P'`-smooth rational. Two open
  bisections through `γ` meet in an open bisection through `γ`.
- **Valuations.** Put `S(a) = {q ∈ P' : v_q(a) = 0}`, so `a ∈ Z_q^×` for `q ∈ S(a)`.
- **Local stability.** If `v_q(a) ≥ 0` for all `q ∈ P'`, then `κ(B(x, m)) = x + a·mẐ ⊆ B(x, m)`
  for every box `B(x, m)` inside the domain, so `γ` is locally stable. Here `B(x, m)`
  means `x + mẐ`.

## Step 2. Upper bound: `𝒫(γ) ⊆ S(a) ⊆ P'`

Let `γ` be locally stable, with a representative `α` equal to `κ` on a neighbourhood
`V` of `x`. Choose a compact open `U_0 ⊆ V` with `α(U_0) ⊆ U_0`; local stability gives one.
Then `𝒫(γ) ⊆ 𝒫(α, U_0)`, and `α = κ` on `U_0` and on all its forward images. Put
`K = K(α, U_0)` and `z = y − x`.

- **Expanding coordinates vanish on `K`.** Let `v_q(a) < 0` and `y ∈ K`. For all `n ≥ 0`,
  `κ^n(y) = x + a^n z` lies in `Ẑ`, as does `x`, so `a^n z_q ∈ Z_q`. This forces `z_q = 0`.
- **Contracting coordinates vanish on `K`.** Let `v_q(a) > 0` and `y ∈ K`. Since
  `α(K) = K`, for every `n` we have `y = κ^n(w)` with `w ∈ U_0`, so
  `v_q(z_q) ≥ n·v_q(a)`. Again `z_q = 0`.
- **Reduction.** So `y ↦ (z_q)_{q ∈ S(a)}` embeds `(K, α)` equivariantly into
  `(∏_{q ∈ S(a)} Z_q, multiplication by a)`. This is an isometry for the max of the
  `q`-adic absolute values.
- **Minimal subsets.** Let `M ⊆ K` be minimal and `y ∈ M`. With `C_S = cl⟨a⟩` in
  `∏_{q ∈ S(a)} Z_q^×`, the orbit closure of `z` is `C_S·z`. So `M` is conjugate to the
  rotation by `a` on `C_S / Stab_{C_S}(z)`.
- **Eigenvalues.** By (R1), the eigenvalue group of `M` is isomorphic to a subgroup of
  `Ĉ_S`, which is a quotient of `⊕_{q ∈ S(a)} (Z_q^×)^∧`. By (R2), its `ℓ`-part is finite
  for every `ℓ ∉ S(a)`.

Hence `𝒫(α, U_0) ⊆ S(a)`. Non-locally-stable germs contribute `∅`. So `𝓘(G) ⊆ P'`.

## Step 3. Lower bound: `P' ⊆ 𝓘(G)` when `P ≠ ∅`

Fix `q ∈ P'` and choose `p ∈ P' ∖ {q}`. This needs `|P'| ≥ 2`, that is `P ≠ ∅`.

- **The germ.** Let `γ` be the germ at `x = 0` of the basic bisection `Z((p, 0), (1, 0))`.
  Its map is `κ(y) = p·y` from `Ẑ` onto `B(0, p)`. By Step 1, `γ` is locally stable.
- **A small invariant core.** Take any pair `(B, U)` in the definition of `𝒫(γ)`. Choose
  a box `B_0 = B(0, m) ⊆ U` on which `α_B = κ`. Then `α_B^n(B_0) = B(0, p^n m)`, and
  `K_0 = ⋂_n B(0, p^n m)` is the set of `y` with `y_p = 0` and `y_{q'} ∈ mZ_{q'}` for
  `q' ≠ p`.
- **It sits inside every core.** `K_0 ⊆ K(α_B, U)`, since `B_0 ⊆ U`. Also `α_B(K_0) = K_0`,
  because `p ∈ Z_{q'}^×` for `q' ≠ p`.
- **A minimal odometer.** Take `y ∈ K_0` with `y_q = m ≠ 0` and all other coordinates
  `0`. Let `C = cl⟨p⟩ ≤ Z_q^×`. The orbit closure of `y` is `M = {c·m : c ∈ C}` in the
  `q`-coordinate, with `0` elsewhere, and `Stab_C(y) = 1` because `Z_q` is a domain. So
  `M` is a minimal subset of `(K(α_B, U), α_B)`, conjugate to rotation by `p` on `C`.
- **Eigenvalues.** `p ≥ 2` is not a root of unity in `Z_q^×`. By (R1) and (R2) the
  eigenvalue group of `M` has infinite `q`-part, so it contains every `q`-power root of
  unity.

So `q ∈ 𝒫(α_B, U)` for every pair `(B, U)`. Hence `q ∈ 𝒫(γ)`, and `q ∈ 𝓘(G)`.

## Step 4. The empty set

If `P = ∅`, then `P' = {2}`.
- **Every core is a point.** Every nontrivial isotropy germ has `a = 2^j` with `j ≠ 0`,
  so `S(a) = ∅`. By Step 2, the core `K(α, U_0)` is `{x}` whenever the germ is locally
  stable.
- **The trivial germ.** For the trivial germ (`a = 1`), minimal subsets are single
  points, and their only continuous eigenvalue is `1`.

So `𝓘(G_{Λ_∅}) = ∅`.

## Step 5. Conclusion

By Steps 2–4, the odd primes in `𝓘(G_{Λ_P})` are exactly `P`. Groupoid isomorphism
preserves `𝓘` (see "The invariant" above). By Matui's Theorem `iso2`, `CT_P(Z) ≅ CT_Q(Z)` gives
`G_{Λ_P} ≅ G_{Λ_Q}`, as in `ct-p-z-isomorphism-type-remembers-the-number-of-primes`. So
`P = Q`.

## Calibration

This recovers the known size result. It does not depend on it, and gives more:
- **Size case.** For `P = {3}` and `Q = {3, 5}`: `𝓘 = {2, 3}` against `{2, 3, 5}`.
- **Equal-size case.** For `P = {3}` and `Q = {5}`: `𝓘 = {2, 3}` against `{2, 5}`. This
  is the smallest instance the earlier node leaves open.
  - The witness for `3` is the germ `×2` at `0`, rotating the `3`-adic core by `2`.
    Here `cl⟨2⟩ = Z_3^×`, since `2` is a primitive root mod `9`, so the minimal pieces
    are odometers of supernatural order `2·3^∞`.
  - The corresponding germ for `Q` gives order `4·5^∞`.
