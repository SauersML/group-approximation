---
rg: 2
id: profinite-skew-layers-collapse-into-the-equicontinuous-factor
kind: claim
title: A skew product of a minimal equicontinuous system by a continuous cocycle into a profinite group is equicontinuous; so profinite layers over the maximal equicontinuous factor collapse, fibre-preserving automorphisms of a row that is proximal over a principal distal layer embed in a connected compact group, a non-exact one needs an infinite-dimensional connected layer, and every lifted translation commensurates the singular set
requires:
  - time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows
  - minimal-system-automorphisms-fix-every-proximal-factor
  - automorphisms-of-hierarchical-rows-are-virtually-abelian
  - quantum-rigid-minimal-topfree-subshift-actions-are-amenable
distinct_from:
  time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows: that shows a non-exact commutant of a rigid row needs infinite fibres over the equicontinuous factor and proposes a profinite distal layer; this proves the profinite layer collapses into the equicontinuous factor, so the layer must be connected and, for a non-exact commutant, infinite-dimensional.
  automorphisms-of-hierarchical-rows-are-virtually-abelian: that bounds Aut for rows finite-to-one over their rotation; this treats rows with infinite fibres and bounds the fibre-preserving part by a compact structure group.
  minimal-system-automorphisms-fix-every-proximal-factor: that kills automorphisms along proximal fibres; this handles the distal layer that remains.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-19; lane proof, elementary; **Referee PASS** bh-ref-q11 2026-09-19, with two repairs to item 3; no priority
claimed). Items 1–4 are standard-style topological dynamics. The recalled inputs are:
- Auslander's structure of equicontinuous minimal systems;
- Michael's zero-dimensional selection theorem;
- Peter–Weyl;
- exactness of finitely generated linear groups (Guentner–Higson–Weinberger).

**What was asked, and the outcome.** The coordinator asked for a rigid minimal free `Z^d`-SFT with
infinite fibres over its maximal equicontinuous factor, and a bound on its automorphism group. It is
**not built here**. Instead, this node closes the profinite form of the door proposed in
`time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows` (which is corrected accordingly), and
pins the remaining target exactly (§ Targets).

## Setting

- `Λ` is finitely generated and acts minimally and equicontinuously on a compact metrizable `M`.
- `L` is the closure of the image of `Λ` in `Homeo(M)`. It is a compact group acting transitively,
  and it preserves a compatible metric `d` (Auslander).
- `K` is a compact metrizable group, and `c : Λ × M → K` is a continuous cocycle:
  `c(λμ, m) = c(λ, μm) c(μ, m)`.
- The **skew product** is `M ×_c K`, with `λ(m, k) = (λm, c(λ, m)k)`. It carries the right
  translations `R_h(m, k) = (m, kh)`, which commute with `Λ`.

## Statement

1. **Profinite skew products are equicontinuous.** If `K` is profinite, then `M ×_c K` is
   equicontinuous. Minimality of `M ×_c K` is not assumed.
2. **Profinite layers collapse into the MEF.** Let `Y` be minimal with maximal equicontinuous factor
   `π : Y → M`. Suppose `π` factors as `Y → Z → M`, where `Z → M` is a principal `K`-bundle: `K` acts
   continuously, freely and on the right, commuting with `Λ`, and its orbits are the fibres. Suppose also:
   - **(S)** `Z/K° → M` has a continuous section. This is automatic when `M` is zero-dimensional, as for
     the odometer factors of all hierarchical, fixed-point and crossing-wire rows.

   Then `K` is **connected**. In particular, a principal profinite layer over the MEF is trivial.
3. **Automorphism face of (RA′), corrected.** Let `Y` and `Z` be as in 2, with `Z` distal and `Y → Z`
   proximal. Let `Aut_0(Y)` be the automorphisms preserving every fibre of `π`.
   - `g ↦ k_g^(-1)` embeds `Aut_0(Y)` into the connected compact group `K`, where `ḡ = R_(k_g)` is the
     map induced on `Z`.
   - Hence, for a finitely generated `G ≤ Aut(Y)`:
     - `G ∩ Aut_0(Y)` is residually finite. It is also linear, hence exact, whenever `K` is a Lie group.
     - A **non-exact** `G` forces `K` to be a connected compact group that is **not Lie**, so it is
       infinite-dimensional (for example `∏_i SU(n_i)`).
   - The door stays open in principle: every residually finite group, Osajda's included, embeds in such a
     `K`.
4. **Lifted translations commensurate the singular set.** Let `Y` be any subshift over `Λ`, `ρ : Y → Z`
   a factor map, and `g ∈ Aut(Y)` covering a homeomorphism `ḡ` of `Z`. Put
   `Z_1 = {z : some y, y' ∈ ρ^(-1)(z) have y(1) ≠ y'(1)}`. Then:
   - `Z_1` is closed, and `Λ·Z_1` is the set of points with non-singleton fibre;
   - `Z_1` is nowhere dense when `ρ` is almost 1-1;
   - if the inverse local rule of `g` has radius `R`, then `ḡ(Z_1) ⊆ ⋃_(|v| ≤ R) v·Z_1`.

   So in the setting of 3, the image of `Aut_0(Y)` in `K` lies in the commensurator
   `Comm(Z_1) = {k ∈ K : Z_1 k ⊆ F·Z_1 and Z_1 k^(-1) ⊆ F·Z_1 for some finite F ⊆ Λ}`.
5. **Calibration.** For a Sturmian coding of a circle rotation, `Z_1` is the pair of partition endpoints
   `{0, β}` (with `β ∉ Zα`). Its commensurator is the rotation group `Zα` up to a finite set, so item 4
   recovers `Aut = ⟨σ⟩` (Olli's theorem, recalled).

## Proof

**1.**
- *One finite level.* Let `N ⊴ K` be open, and `c_N = c mod N`.
  - For `s` in a finite symmetric generating set `S`, the map `c_N(s, ·)` is locally constant, hence
    constant on `ε`-balls for some `ε > 0`.
  - The set `U = {u ∈ L : d(um, m) < ε for all m}` is a symmetric open neighbourhood of `1`.
  - `⟨U⟩` is an open subgroup, so it has finite index in the compact `L`. Its normal core `L_0` is again
    open, normal and of finite index. Each `c_N(s, ·)` is `L_0`-invariant.
- *Invariance for all `λ`.* By the cocycle identity, `c_N(sμ, um) = c_N(s, μum) c_N(μ, um)`, and
  `μum = (μuμ^(-1))μm` with `μuμ^(-1) ∈ L_0`. So induction on word length makes every `c_N(λ, ·)`
  `L_0`-invariant.
- *Reduction to a finite system.* `F_0 = L_0\M` is finite, and `Λ` acts on it, because `L_0` is normal.
  - `F_N = F_0 × K/N`, with `λ(f, κ) = (λf, c̄_N(λ, f)κ)`, is a finite `Λ`-set.
  - `(m, kN) ↦ (m, (L_0m, kN))` is an equivariant embedding of `(M ×_c K)/N` onto a closed invariant
    subset of `M × F_N`, which is equicontinuous. So `(M ×_c K)/N` is equicontinuous.
- *Inverse limit.* Take open normal `N_1 ⊇ N_2 ⊇ ⋯` with trivial intersection. Then `M ×_c K` embeds
  equivariantly in `∏_j (M ×_c K)/N_j`, and a countable product of equicontinuous systems is
  equicontinuous. ∎

**2.**
- `K/K°` is compact and totally disconnected, hence profinite, and it acts freely on `Z̄ = Z/K°` with
  orbits the fibres over `M`.
- *A skew product.* A section `s` from (S) gives the homeomorphism `M × K/K° → Z̄`, `(m, k) ↦ s(m)k`.
  The cocycle `λ s(m) = s(λm) c(λ, m)` is continuous, because the division map on the fibre product is
  continuous. So `Z̄` is a skew product.
- *(S) over zero-dimensional `M`.* The orbit map of a compact group action is open. So `m ↦` (fibre over
  `m`) is lower semicontinuous with compact values, and Michael's zero-dimensional selection theorem
  gives `s`.
- *Collapse.* By 1, `Z̄` is equicontinuous, and it is a factor of `Y` lying over `M`. By maximality of
  `M`, `Z̄ → M` is an isomorphism. Its fibres are `K/K°`-torsors, so `K/K° = 1`. ∎

**3.**
- *`g` descends.* Let `ρ : Y → Z`. Proximal pairs of `Y` map to proximal pairs of the distal `Z`, which
  are equal, so `P(Y) ⊆ R_ρ`. `Y → Z` is proximal, so `R_ρ ⊆ P(Y)`. Hence `R_ρ = P(Y)`, and every
  automorphism preserves it, so `g` induces `ḡ` on `Z`.
- *`ḡ` is a right translation.* `ḡ` preserves each `K`-orbit, so `ḡ(z) = zκ(z)` with `κ` continuous.
  Commuting with `Λ` and freeness give `κ(λz) = κ(z)`, so `κ` is constant, `= k_g`, by minimality. Then
  `k_(gh) = k_h k_g`.
- *Injectivity.* If `k_g = 1`, then `(y, gy) ∈ R_ρ` is proximal, and `g = id` by item 3 of
  `minimal-system-automorphisms-fix-every-proximal-factor`.
- *The consequences.*
  - `K` embeds in a product of unitary groups (Peter–Weyl), so its finitely generated subgroups are
    residually finite (Malcev).
  - A compact Lie group is linear, and finitely generated linear groups are exact.
  - For a finitely generated `G ≤ Aut(Y)`, the quotient `G/(G ∩ Aut_0(Y))` embeds in the abelian group
    `Aut(M, Λ)` when `Λ` is abelian (the parent node). So non-exactness passes to `G ∩ Aut_0(Y)`.
  - A connected compact group that is not Lie is infinite-dimensional.
  - For the embedding claim: a residually finite `G` embeds in `∏ Q_i` over finite quotients, and each
    `Q_i ↪ U(|Q_i|) ↪ SU(|Q_i| + 1)` by `A ↦ diag(A, det A^(-1))`.

**4.**
- *Closed.* If `z_n → z` with witnesses `y_n, y'_n`, pass to limits `y, y'`. They lie over `z` and still
  differ at `1`.
- *Singular points.* With `(λy)(h) = y(λ^(-1)h)`, the points `y` and `y'` differ at `v` iff `v^(-1)y` and
  `v^(-1)y'` differ at `1`. So `z` is singular iff `v^(-1)z ∈ Z_1` for some `v`.
- *Nowhere dense.* When `ρ` is almost 1-1, the points with singleton fibre are dense and miss `Z_1`.
- *The inclusion.* For `z ∈ Z_1` with witnesses `y, y'`, the points `gy` and `gy'` lie over `ḡz`. They
  differ somewhere in `B_R`, since otherwise the inverse rule would give `y(1) = y'(1)`. So
  `ḡz ∈ v·Z_1` with `|v| ≤ R`. Apply this to `g^(-1)` as well.

**5.** The endpoints of a Sturmian partition are `{0, β}`. A lifted rotation `t` must carry them into
finitely many translates `{nα, β + nα}`, which forces `t ∈ Zα` up to a finite set. ∎

## The coordinator's candidates, and the RWM door

- **Robinson, Mozes and DRS substitution or fixed-point tilings, and the crossing-wire shift.**
  - These rows have odometer MEFs and are finite-to-one over them, so `Aut` is virtually abelian
    (`automorphisms-of-hierarchical-rows-are-virtually-abelian`).
  - By item 2, even an infinite profinite distal layer over their odometer would collapse.
  - Hierarchical, profinite structure therefore cannot host a non-exact commutant, in any coding.
- **Hochman-type realizations.** Barbieri–Carrasco-Vargas–Rojas (arXiv:2401.07973, abstract read) make
  effective systems beyond dimension zero into factors of SFTs, for many groups. That is the natural source
  of an SFT `Y → Z` with a connected layer `Z = M ×_c K`. Rigidity of such simulations is known only
  through the fixed-point (crossing-wire) mechanism, which allows no free data.
- **The RWM door (b) is not closed by clustering alone.**
  - The end shift of `F_n` is quantum rigid, proximal and topologically weakly mixing (the last is
    recalled). So over non-amenable groups, relatively weakly mixing infinite fibres coexist with
    rigidity.
  - Being proximal, its `Aut` is trivial.
  - What an automorphism needs is a fibre of **pairwise distal** points (the proximal node, item 3).
  - Over `Z^d`, a kill of door (b) must use amenability.

## Targets (for bh-ra-counter; replaces the profinite target of the parent node)

- **T1 (calibration, first rigid row with non-amenable Aut).**
  - Find a rigid, minimal, free `Z^2`-SFT that is almost 1-1 over a minimal, non-equicontinuous
    `Z = M ×_c SU(2)`.
  - A dense free subgroup of right translations must commensurate `Z_1` (item 4).
  - It would give `F_2 ≤ Aut(Y)`, and so a rigid minimal free SFT over `F_2 × Z^2`. That group is exact,
    so it is only a calibration.
- **T2 (refutes (RA′)).** The same with `K = ∏_i SU(n_i)` and `G_0 ⊇` Osajda's residually finite
  non-exact group.
  - Then `G_0 × Z^2` carries a rigid minimal free SFT, and (RA′) fails (parent node, item 1).
  - If moreover `G_0` sits inside a finitely presented `Λ_1 ≤ Aut(Y)`, then `Λ_1 × Z^2` is a carrier.
- **The equation to solve.** `Z_1 k ⊆ F_k·Z_1` for a dense subgroup of `K`, with `Z_1` the closed
  singular set of a rigid coding.

## Lesson for general BH

**Hierarchy is profinite, and profinite structure is invisible to commutants.**
- A continuous cocycle into a profinite group over an equicontinuous base only ever sees finitely many
  levels at a time. So the skew product is again equicontinuous and folds into the maximal equicontinuous
  factor.
- Every profinite, hierarchical or odometer-type layer of a rigid row is therefore already part of its
  rotation, and it contributes only abelian automorphisms.
- A non-exact commutant, which (RA′) must forbid and a time-lift counterexample must supply, has to act
  through a **connected, infinite-dimensional** compact layer (twisted, Anzai-type dynamics). Every
  lifted element must commensurate the coding's singular set.

This moves the (RA′) counter-search away from substitutions and odometers, and toward rigid codings of
twisted continuous systems. Those are the systems that SFT realizations beyond dimension zero now make
available.

## Referee (bh-ref-q11, 2026-09-19): PASS for items 1, 2, 4, 5; item 3 needs two repairs to its reasoning (conclusions stand)

**Item 1: correct.**
- `c_N(s,·)` is constant on `ε`-balls, by a Lebesgue number of the finite clopen partition. So it is `⟨U⟩`-invariant, hence `L_0`-invariant.
- The induction uses normality of `L_0` exactly as written.
- `F_0` is finite because `L` is transitive and `L_0` has finite index.
- The embedding into `M × F_N` is equivariant.
- The countable inverse limit is fine, since profinite metrizable `K` has a basis of open normal subgroups.

**Item 2: correct.**
- `K/K°` acts freely on `Z/K°`.
- The division map is continuous for free actions of compact groups.
- Michael's zero-dimensional selection theorem applies, since the orbit map is open, so fibres vary lower semicontinuously.
- Maximality of the MEF gives `ψ : M → Z̄` with `ψ` and `Z̄ → M` mutually inverse.

**Item 3: sound, with two repairs to the reasoning.**
- **Sound as written.**
  - `R_ρ = P(Y)`.
  - `κ` is continuous, `Λ`-invariant, hence constant.
  - `k_(gh) = k_hk_g`.
  - Injectivity has a one-line proof: `py = pgy` for some `p ∈ βΛ` gives `g(py) = py`, so `g` fixes a point and is the identity by minimality.
  - The extension step, since exact-by-amenable is exact.
- **(R1) "A connected compact group that is not Lie is infinite-dimensional" is false.** Solenoids are 1-dimensional, connected, compact and not Lie. The conclusion still holds, for a different reason.
  - A finite-dimensional compact connected `K` is `(Z(K)° × S)/Δ`, with `S` a compact semisimple Lie group and `Δ` central.
  - So every subgroup of `K` is abelian-by-(subgroup of the linear group `K/Z(K)°`), hence exact (GHW for countable linear groups, then extension).
  - So a non-exact `G ∩ Aut_0(Y)` forces `K/Z(K)°`, and hence `K`, to be infinite-dimensional.
  - Replace "not Lie" by "`K/Z(K)°` is not Lie".
- **(R2) "`G ∩ Aut_0(Y)` is residually finite"** holds for its finitely generated subgroups (Malcev on each unitary factor).
  - It can fail for non-finitely-generated subgroups of compact groups: `Q/Z ≤ U(1)`.
  - `G ∩ Aut_0(Y)` need not be finitely generated.
  - None of the later uses needs more than the finitely generated case.

**Item 4: correct.**
- `Z_1` is closed by compactness.
- The inclusion `ḡ(Z_1) ⊆ ⋃_(|v|≤R) vZ_1` follows from the radius of `g^{-1}`, with the action convention `(λy)(h) = y(λ^{-1}h)`.

**Item 5: the calibration is consistent.** A translation carrying `{0,β}` into finitely many translates `{nα, β+nα}` lies in `Zα`, generically.

The candidate discussion and the targets are commentary; I did not referee them.
