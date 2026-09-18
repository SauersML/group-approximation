---
rg: 2
id: algebraic-interval-exchange-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated group of interval exchanges, with or without flips, with real algebraic lengths and translations embeds in a finitely presented simple group; so do all subgroups of the Stein groups V(Z[u],⟨u⟩,ℓ) for suitable units u of every real number field
requires:
  - negative-base-pisot-stein-groups-are-contracting-rsgs
  - flip-codings-remove-the-sign-obstruction-for-iet-groups
distinct_from:
  pisot-interval-exchange-groups-satisfy-boone-higman: that covers fields containing an (F) unit, those with an isolated-sign unit, and so misses Q(√3); this covers every real number field, through negative-base codings.
  quadratic-rotation-iet-groups-satisfy-boone-higman: that (bh-free-03) covers IET(Z+αZ) for quadratic α via substitutions; this covers every rank and every real algebraic field.
  fp-simple-groups-have-no-interval-exchange-action: that forbids finitely presented infinite simple groups from acting by interval exchanges; the hosts here contain interval exchange groups but act with nontrivial slopes and flips.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed).

**Inputs read at source:**
- the shift-radix-system set-of-witnesses theorem: Brunotte; ABBPT, Acta Math. Hungar. 108 (2005), Theorem 5.1, as
  stated in the SRS survey arXiv:1312.0386;
- the conjugacy between `{γx}` on `Z[γ] ∩ [0,1)` and the SRS of the cofactor of `x − γ`: Hollander, as
  Proposition `prop:betanumformula` of that survey, and KSV (arXiv:1701.04609, Proposition `p:conjugacy2`, with
  `α = 0`). Neither proof uses the sign of the base; it is applied here to `γ = −β`, and re-derived below.

## Statement

1. **Suitable units exist in every real field.** Let `K` be a real number field, of degree `d`. Then `K = Q(β)`
   for a Pisot unit `β` satisfying (F−₀), the finiteness of `y ↦ {−βy}` on `Z[β] ∩ [0,1)`.
2. **Interval exchanges.** Let `G` be a group of interval exchanges of an interval, with or without flips
   (bijections off finitely many points, piecewise `y ↦ ±y + t`). Suppose its lengths and translations generate a
   finitely generated group of real algebraic numbers, which is automatic when `G` is finitely generated. Then `G`
   embeds in a finitely presented simple group. This includes:
   - Sturmian Juschenko--Monod groups for every algebraic angle;
   - derived full groups of minimal interval exchanges with algebraic lengths, of any rank;
   - `IE(Γ)` for every finitely generated `Γ ⊂ Q(√3)`, a field outside the positive-base route.
3. **Stein groups.** For `β` as in item 1, every subgroup of `V(Z[β],⟨β⟩,ℓ)`, and of its flip version `G^±_β`,
   embeds in a finitely presented simple group. `G^±_β` is itself finitely presented.

## Proof

1. **Units.**
   - **Choice.** If `K = Q`, replace it by a real quadratic field. By item 1 of
     `flip-codings-remove-the-sign-obstruction-for-iet-groups`, with `δ = 1/(4(d−1))` and `φ = π/(3(d−1))`, take a
     unit `β > 1` with `Q(β) = K` whose other conjugates `β_j` satisfy `Σ|β_j| ≤ 1/4` and `|arg β_j| ≤ φ`. Then
     `β = ∏|β_j|^{−1} ≥ 4`, and `β` is Pisot.
   - **Positive symmetric functions.** Let `e_k` be the elementary symmetric functions of the `β_j`, and `E_k` the
     same sums of absolute values. Each product of `k` of the `β_j` has argument at most `kφ ≤ π/3`. So `e_k` is
     real with `e_k ≥ E_k/2 > 0`. Also `E_{k+1} ≤ E_k·Σ|β_j|/(k+1) ≤ E_k/4`. Hence `e_{k+1} ≤ e_k/2`.
   - **The polynomial of −β.** The minimal polynomial of `−β` is `(x + β)Q(x)` with `Q(x) = ∏_j(x + β_j)`. Write
     `Q(x) = x^{d−1} + r_{d−2}x^{d−2} + … + r_0`. Then `r_{d−1−k} = e_k`, so `0 < r_0 < r_1 < … < r_{d−2} ≤ 1/4`.
   - **SRS conjugacy.** Put `r_{d−1} = 1`. Then `{r_i}` is a Z-basis of `Z[β]`, and `−βr_i = r_{i−1} − c_i` with
     `c_i ∈ Z` and `r_{−1} = 0`, by comparing coefficients.
     - So `φ(z) = Σ_{i<d−1} r_i z_i − ⌊Σ r_i z_i⌋` is a bijection `Z^{d−1} → Z[β] ∩ [0,1)`.
     - It conjugates the SRS `τ_r(z) = (z_1, …, z_{d−2}, −⌊rz⌋)` to `T'`.
     - So (F−₀) holds iff `r ∈ D^0_{d−1}`.
   - **Witness lemma: `0 < r_0 < … < r_{d−2} < 1` implies `r ∈ D^0_{d−1}`.**
     - Let `V` be the vectors in `{−1,0,1}^{d−1}` whose consecutive nonzero entries alternate in sign. It contains
       `±e_i`.
     - For `z ∈ V ∖ 0` with last nonzero entry `z_j`, the alternating sum `rz` has the sign of `z_j` and
       `0 < |rz| ≤ r_j < 1`.
     - So the appended entry `−⌊rz⌋` is `0` if `z_j = 1` and `1` if `z_j = −1`. Hence `τ_r(V) ⊆ V` and
       `−τ_r(−V) ⊆ V`, and `V` is a set of witnesses.
     - Every `z ∈ V` reaches 0: after the last nonzero entry becomes `+1`, only zeros are appended.
     - Brunotte's theorem gives `r ∈ D^0_{d−1}`.
2. **Interval exchanges.**
   - The lengths and translations generate a finitely generated `Γ ⊆ K`, where `K` is the real number field
     they generate.
   - Choose `β` by item 1, and `N` with `NΓ ⊆ Z[β]`.
   - Rescaling by `N`, and then by `β^{−m}` into `[0,1)`, embeds the group in `G^±_β`, as in
     `pisot-interval-exchange-groups-satisfy-boone-higman`. Without flips the image lies in `V(Z[β],⟨β⟩,1)`; flipped
     pieces `y ↦ −y + c` stay in `G^±_β`.
   - `β ≥ 4 > 2`, so apply `negative-base-pisot-stein-groups-are-contracting-rsgs`.
3. **Stein groups.** Item 3 is that node's statement. ∎

## Lesson for general BH

Every finitely generated real algebraic piecewise-translation group has a Boone--Higman host, and the proof uses
no group theory of the input.
- A Dirichlet-plus-simultaneous-approximation choice of unit gives a coding whose finiteness is a one-line witness
  argument.
- Pisot compactness gives the finite nucleus.

For general BH this brackets the arithmetic full-group route:
- noncomputable slope modules cannot embed (`stein-derived-groups-need-computable-modules`);
- algebraic data always embeds, whatever the sign pattern of the units.

Transcendental computable data (`transcendental-slope-thompson-groups-satisfy-boone-higman`) is the frontier.
There the Pisot finiteness engine has no input, so a host must come from some other source of compactness.
