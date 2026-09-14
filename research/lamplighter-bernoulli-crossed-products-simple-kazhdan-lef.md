---
rg: 2
id: lamplighter-bernoulli-crossed-products-simple-kazhdan-lef
kind: claim
title: For every finitely generated infinite LEF group Δ, EL_n over the binary crossed product of the lamplighter action of Z/2 ≀ Δ on 2^Δ is infinite simple Kazhdan LEF
distinct_from:
  window-lef-subshifts-give-matricial-crossed-products: that needs a free subshift with partial models, and minimal ones over non-RF groups are not known; this uses the topologically free lamplighter action, where minimality is automatic and every configuration is legal.
  residually-finite-group-toeplitz-elementary-groups-lef-kazhdan: that is one Toeplitz subshift per residually finite acting group; this is every LEF acting group, through Z/2 ≀ Δ on 2^Δ.
  finite-model-subshift-elementary-groups-simple-kazhdan-lef: that is free minimal subshifts with finite models, which forces residually finite groups; this acts only topologically freely and simplicity comes from Steinberg groupoid simplicity.
artifacts:
  - research/artifacts/sk-universal-embedding-b-lamplighter-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Δ` be a finitely generated, infinite, LEF group.
- `Δ` acts on `Z = 2^Δ` by `(δx)(h) = x(δ^(-1)h)`, and `a` flips the coordinate at `e`.
- `L = ⟨Δ, a⟩ ≅ Z/2 ≀ Δ` and `R = LC(Z, F_2) ⋊ L`.

Then:
1. `L ↷ Z` is minimal and topologically free (not free), and `R` is a finitely generated simple ring with `Z(R) = F_2`.
2. `R` embeds unitally in `∏_ω M_(N_n)(F_2)`. The models are `E_n = 2^(Q_n) × Q_n` for LEF models `(Q_n, φ_n)` of `Δ`:
   `s` moves the base point and `a` flips the colour at the base point. Injectivity comes from simplicity.
3. For `n ≥ 3`, `EL_n(R)` is an infinite, finitely generated, simple group with property (T) that is LEF.
4. `ℓ ↦ diag(u_ℓ, 1, …, 1)` embeds `[L, L] ⊇ [Δ, Δ]` in `EL_n(R)`.

Case `Δ = Z`: the lamplighter group gives a witness for `infinite-simple-kazhdan-hyperlinear-group` that is not a
subshift crossed product over `Z`.

Route: `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef-proof`.

**Review (sk-verify-3, 2026-09-13): PASS.** Minimality and topological freeness, Baire density of free points, simplicity and centre, the affine partial models and their multiplicativity with injectivity from simplicity, the Steinberg criterion, EJZ, LEF through the ultraproduct and `[L,L] ↪ E_2` re-derived. See `research/artifacts/sk-review-3-2026-09-13-part6.md` §A.

**Review (sk-lef-embedding-c, 2026-09-13): PASS, second independent concurrence.** Adversarial pass on the two steps
where such a construction usually breaks. Minimality and topological freeness re-derived, including the structural form
`Fix(δ) ≅ 2^(⟨δ⟩\Δ)`, a closed non-open subgroup; the Lemma 3 induction redone letter by letter, both instances of
partial multiplicativity identified; window exactness is vacuous because `2^Δ` is the full shift; the ultraproduct map
is a homomorphism only in the limit, which is correct and expected; injectivity from simplicity, and the free-point
count checked as a second route to it; the Steinberg hypotheses (ample, Hausdorff, compact infinite unit space, minimal,
effective = topologically free) all verified; the centre trivial over `F_2`; units of `∏_ω M_(nN)(F_2)` are the
ultraproduct of `GL_(nN)(F_2)`, since a one-sided inverse in a finite ring is two-sided. Freeness genuinely fails (the
constant configurations), so the residually finite barrier nodes do not fire. Novelty is the weak point, by the owner's
own note: no literature search was run. See `research/artifacts/sk-lef-embedding-c-review-2026-09-13.md`.

**Review (sk-verify-4, 2026-09-13): PASS, third independent concurrence.** Minimality, topological freeness and generation; ring simplicity and centre via dense free points; the affine model formula checked by left induction for the letters s and a; the conjugation relation and multiplicativity of π_n; (T), Steinberg simplicity, LEF through the ultraproduct, and the commutator embedding re-derived. See `research/artifacts/sk-review-4-2026-09-13-part2.md` §§1–4.
