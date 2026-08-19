# Compression collapse and exact MF radicals of permutational wreath products

Status: **proposed theorem suite, adversarially audited in-session, not yet
externally refereed; no literature-priority claim.**  The group-theoretic
layer and the scaled transport theorem are kernel-checked
(`Sofic/ScaledKazhdanTransport.lean`, `Sofic/TorsionCompressionCollapse.lean`);
the analytic collapse core is paper-level, and — since Delorme's theorem
(`Kazhdan/DelormeFixedPoint.lean`) and Kazhdan finite generation
(`Kazhdan/KazhdanFiniteGeneration.lean`) are already kernel-checked in-repo
— its remaining unformalized ingredients are packaging, not classical
inputs (§9).  Nothing here touches the manuscript or the frozen
Theorem A--E trust surface.

This document supersedes the session-draft "Compression Collapse and the MF
Radical of Permutational Wreath Products" (user draft, 2026-08-14): every
theorem there survives audit and is strictly generalized here; the repairs
and deltas are recorded in §8.

---

## 1. The maximal pointwise theorem

Everything happens inside one ambient countable group and one corona
representation; no wreath product, no group action, no transitivity, and no
global structure is assumed.  Throughout, *corona* means the norm matrix
corona `∏ M_{d_n}(ℂ) / ⊕ M_{d_n}(ℂ)` for an arbitrary positive dimension
sequence (`NormMatrixCStarCorona` / `NormMatrixCoronaUnitary` in the repo,
with the polar-correction equivalence between the two models).

**Theorem 1 (compression--torsion collapse, pointwise form).**
Let `W` be a countable group and `π : W → U(Q)` a homomorphism into the
unitary group of a norm matrix corona.  Let

* `Λ ≤ W` have Kazhdan property (T);
* `s ∈ W` be a one-sided compressor of `Λ`: `s Λ s⁻¹ ≤ Λ`;
* `k ∈ W` satisfy the three **image-side** hypotheses
  1. `π(k)` has finite order `m ≥ 1`;
  2. the orbit images `{ π(λ k λ⁻¹) : λ ∈ Λ }` pairwise commute;
  3. `π(h k h⁻¹) = π(k)` for every `h ∈ s Λ s⁻¹`.

Then

```
π(λ k λ⁻¹) = π(k)   for every λ ∈ Λ.
```

Equivalently, `π(⁅λ, k⁆) = 1` for all `λ ∈ Λ`: the entire `Λ`-conjugation
orbit of `k` is collapsed to a single corona element.

Remarks on maximality.

* All three hypotheses on `k` are conditions on the **image** `π(k)`.  In
  particular `k` itself need not be torsion, the orbit need not commute in
  `W`, and hypothesis (3) is weaker than `[sΛs⁻¹, k] = 1`.  The group-side
  special case (`k^m = 1`, commuting orbit, centralized by the compressed
  copy) is the Lean-side witness predicate
  `IsTorsionCompressionWitness` in `Sofic/TorsionCompressionCollapse.lean`.
* Because hypothesis (3) is itself of the form "π identifies an orbit",
  the theorem is a **closure operator**: collapses established at one stage
  become hypothesis (3) for further stages.  §3 exploits this.
* The hypotheses never mention how `k` sits globally in `W`; wreath lamps,
  Clifford-type coordinates satisfying commutation only in the image, and
  markers of central extensions all qualify when their images do.
* Two further hypotheses relativize to the image as well.  (a) The
  compression relation may be taken modulo `ker π`: if
  `π(s)π(λ)π(s)⁻¹ ∈ π(Λ)` for each `λ`, the conjugation-defect estimate of
  the corner argument still vanishes in operator norm (the discrepancy is
  a corona-trivial unitary), and nothing else uses exact compression.
  (b) Property (T) is needed only for the image group `π(Λ)` (equivalently
  `Λ/(Λ ∩ ker π)`): every averaging estimate factors through it.  The Lean
  interface (`KazhdanCompressionCore`) keeps the group-level form; the
  π-relative forms are ladder items, not used below.

The special case recovering the user draft's Theorem A: `W = K^{(X)} ⋊ G`
a permutational wreath product, `Λ = Γ` with `X = G/Γ`, `k = k_{x₀}` the
lamp at `x₀ = sΓ`.  There hypothesis (2) holds because distinct lamp
coordinates commute, hypothesis (3) because `sΓs⁻¹` fixes `x₀`, and
hypothesis (1) because `k ∈ K` is torsion.  None of the wreath structure
enters the proof.

## 2. Proof of Theorem 1

Fix `π`, lift it: choose unitaries `U_{g,n} ∈ U(d_n)` representing `π(g)`,
asymptotically multiplicative in operator norm on each pair (this is the
`OpAlmostRepresentation` extraction already used by the repo's kill
theorems).  Write `H = sΛs⁻¹` and `v_λ = π(λkλ⁻¹)`.

**Step 1: exact commuting finite-spectrum lifts.**  The countable family
`{v_λ}` consists of commuting `m`-torsion unitaries in the corona.  Their
spectral projections `e_{λ,j} = m⁻¹ Σ_ℓ ζ^{-jℓ} v_λ^ℓ` (`ζ = e^{2πi/m}`)
form a countable commuting family of projections.  Lift them to commuting
projections `e_{λ,j,n}` (inductive averaging over the finite Boolean algebra
of the previously lifted projections, then a spectral cut at `1/2`; each
step preserves commutation with all earlier lifts and the corona class).
For each fixed `λ` the partition relations `e_{λ,j}e_{λ,r} = 0 (j≠r)`,
`Σ_j e_{λ,j} = 1` hold in the corona; since products and sums of the
commuting lifts are again projections, whose norms tend to `0` resp. `1`,
the relations hold **exactly** for all large `n`; setting the finitely many
exceptional coordinates of each `λ` to the trivial partition changes
nothing in the corona and keeps global commutation.  Define the exact
commuting `m`-torsion lifts `v_{λ,n} = Σ_j ζ^j e_{λ,j,n}`.

Two consequences used repeatedly:

* (Rigidity of exact lifts)  If `‖v_{λ,n} − v_{μ,n}‖_{op} < η_m
  := min_{i≠j}|ζ^i − ζ^j|` then `v_{λ,n} = v_{μ,n}`: the difference is
  normal with spectrum in `{ζ^i − ζ^j}`.  In particular hypothesis (3)
  gives, for each `h ∈ H`, `v_{h,n} = v_{1,n}` for all large `n`.
* (Rank metric)  `d_n(λ,μ) := rank(v_{λ,n} − v_{μ,n})` is the number of
  joint-eigenbasis sites where the `ℤ/m` labels of `v_{λ,n}` and `v_{μ,n}`
  differ; it is a pseudometric, and
  `η_m² · d_n(λ,μ) ≤ Tr|v_{λ,n} − v_{μ,n}|² ≤ 4·d_n(λ,μ)`.

**Step 2: eventual invariance.**  Covariance
`‖U_{g,n} v_{λ,n} U_{g,n}^* − v_{gλ,n}‖ → 0` holds for each fixed `g`
(from `π(g)π(λkλ⁻¹)π(g)⁻¹ = π(gλk(gλ)⁻¹)`; here `gλ` abbreviates the orbit
index of `gλk λ⁻¹g⁻¹`).  Applying it to the disagreement projections
(polynomials in the `v`'s) and using that projections at operator distance
`< 1` have equal rank: for each fixed `g, λ, μ`,
`d_n(gλ, gμ) = d_n(λ, μ)` for all large `n`.

**Step 3: normalization by a full generating set.**  Property (T) makes
`Λ` finitely generated — kernel-checked in-repo as
`fg_of_hasKazhdanPropertyT` (`Kazhdan/KazhdanFiniteGeneration.lean`), and
`HasKazhdanPropertyT` bundles a finite symmetric generating Kazhdan pair.
Fix such a set `S` and put

```
k_n = Σ_{a∈S} d_n(1, a).
```

For any `λ ∈ Λ` of `S`-word length `r`, the triangle inequality and Step 2
give `d_n(1, λ) ≤ r·k_n` for all large `n`.  **This replaces the special
relative generator of the preliminary; it is the decisive move and is
scale-robust.**

Assume the conclusion fails: some `λ₀` has `π(λ₀kλ₀⁻¹) ≠ π(k)`, so by the
rigidity of exact lifts `d_n(1, λ₀) ≥ 1` infinitely often; by the word
bound, `k_n ≥ 1` on that subsequence.  Fix a nonprincipal ultrafilter `ω`
concentrated on it.

**Step 4: the rescaled Hilbert space and the cocycle.**  Let `K_ω` be the
ultraproduct of `(M_{d_n}(ℂ), Tr(·^*·)/k_n)` along `ω`, and
`σ(g) = Ad(U_{g,n})` the induced genuine unitary representation of `W`
(rescaling does not change `‖Ad(U)−Ad(V)‖ ≤ 2‖U−V‖_{op}`).  Set

```
c_n(λ) = v_{λ,n} − v_{1,n},     c(λ) = [(c_n(λ))] ∈ K_ω   (λ ∈ Λ).
```

Well-defined: `Tr|c_n(λ)|² ≤ 4·d_n(1,λ) ≤ 4r·k_n`.  Cocycle identity
`c(aλ) = c(a) + σ(a)c(λ)`: the defect
`D_n = U_{a,n}c_n(λ)U_{a,n}^* − (c_n(aλ) − c_n(a))` has operator norm
`→ 0` (covariance) and rank `≤ 2·d_n(1,λ) ≤ 2r·k_n` (Step 2), hence
rescaled mass `Tr|D_n|²/k_n ≤ 2r‖D_n‖² → 0`.  **The rank×op²≥mass
interface is what makes every step of this argument survive the `k_n`
scale; it is the same interface (`hsDistSq_le_sq_l2_opNorm`,
`vecMass_mulVec_le`) that the repo's kill theorem uses at the dimension
scale.**

By construction `Σ_{a∈S} ‖c(a)‖² ≥ η_m² · lim_ω (k_n/k_n) = η_m² > 0`, so
`c ≠ 0`; and `c(h) = 0` for every `h ∈ H ∩ Λ`-word — indeed for every
`h ∈ H`, exactly, by Step 1.

**Step 5: (T) coboundary.**  `σ|_Λ` is a genuine unitary representation on
the Hilbert space `K_ω`; view it as an orthogonal representation of the
underlying real Hilbert space (or restrict to the closed span of the
`σ(Λ)`-orbit of the cocycle values; both are complete).  Delorme's theorem
— kernel-checked in-repo as
`Delorme.exists_fixed_point_of_hasKazhdanPropertyT`
(`Kazhdan/DelormeFixedPoint.lean`, via the Gaussian positive-definite
kernel) — gives `w ∈ K_ω` with `c(λ) = σ(λ)w − w`.  Since `c|_H = 0`, `w`
is `H`-fixed.

**Step 6: scaled matricial Mautner.**  Claim: `w` is `Λ`-fixed; then
`c ≡ 0` on `Λ`, contradicting Step 4 and proving the theorem.

Since `s⁻¹Hs = Λ`, the vector `u := σ(s)⁻¹w` is exactly `Λ`-fixed
(`σ(λ)σ(s⁻¹)w = σ(s⁻¹)σ(sλs⁻¹)w = σ(s⁻¹)w`).  So it suffices that the
**forward transport** `σ(s)u = w` of an exactly-`Λ`-fixed vector is again
`Λ`-fixed.  At the sequence level this is precisely the scaled Kazhdan
transport theorem, now kernel-checked:

> `ScaledKazhdanTransport.scaled_transport` /
> `scaled_transport_star` / `compressionGroup_scaled_transport_both`:
> for **every** nonnegative weight `w : ℕ → ℝ`, every sequence `x_n` with
> `Tr|x_n|² = O(w_n)` that asymptotically commutes with the Kazhdan image
> at scale `w` (i.e. `Tr|x_n − Ad(U_{γ,n})x_n|² ≤ ε·w_n` eventually, for
> each `γ`) is carried by each one-sided compressor, in both directions,
> to another such sequence.

The finite-level chain behind it (`transported_displacement_le`,
`one_sub_corner_mul_moved_vanishing`) is per-`n` and quantitative, so it
applies verbatim along the ultrafilter: `ω`-eventual hypotheses give
`ω`-eventual conclusions.  Every vector of `K_ω` is mass-bounded at scale
`k_n` by definition of the ultraproduct, so the mass-sector restriction is
no restriction here.  This discharges the "arbitrary scalar rescaling"
step of the preliminary: **the Mautner input holds at every scale on the
mass-bounded sector, and only the mass-bounded sector ever occurs.** ∎

Two structural notes.

* The dimension-normalized transport needs an operator-norm bound on the
  commutant sequence; at general scales the correct hypothesis is the mass
  bound, which is weaker at the dimension scale
  (`IsUniformlyBounded.isScaledMassBounded_card`) and exactly right at rank
  scales.  This is the precise sense in which rank-blindness is evaded:
  the argument never measures the lamps themselves (mass `≈ d_n`), only
  their differences (mass `O(k_n)`).
* Property (T) is used **three** times: finite generation (Step 3), FH
  (Step 5), and the Kazhdan-pair spectral gap inside the transport
  (Step 6).  §7 shows none of the three is removable.

## 3. Globalization: expansion closure

The pointwise theorem globalizes by pure group theory, now kernel-checked
in `Sofic/TorsionCompressionCollapse.lean`:

* For a homomorphism `f : E → Q` and marked `k`, the set
  `{g : f(gkg⁻¹) = f(k)}` is a subgroup (`piConjStabilizer`).
* (`expansionSubgroup_le_piConjStabilizer`)  If for each `s` in a family
  `T` of compressors the collapse `f(γ·(sks⁻¹)·γ⁻¹) = f(sks⁻¹)` holds for
  all `γ ∈ L`, then the **expansion subgroup**
  `L↑_T := ⟨ s⁻¹ L s : s ∈ T ⟩` stabilizes `k` itself:
  `f(jkj⁻¹) = f(k)` for all `j ∈ L↑_T`.

With Theorem 1 supplying the hypothesis at each compressor (note
`s(sΛs⁻¹)s⁻¹ ≤ sΛs⁻¹`, so all powers `s^j` are compressors, as is any
family, and different Kazhdan subgroups `Λ_i` with compressors `s_i` may
be mixed), the corona-forced identification of `k` extends to the full
expansion closure — and, iterating the closure remark of §1, to the
transfinite collapse closure.

**Theorem 2 (wreath form).**  Let `G` be countable, `X` a `G`-set,
`K` countable, `W = K^{(X)} ⋊ G`, and `π` a corona representation of `W`.
Let `Λ ≤ G` be Kazhdan, `s ∈ G` with `sΛs⁻¹ ≤ Λ`, and let `x₀ ∈ X` be
**any** point whose stabilizer contains `sΛs⁻¹`.  Then for every torsion
`k ∈ K`:

```
π(k_{λx₀}) = π(k_{x₀})   for all λ ∈ Λ.
```

Consequently, with `Γ = G_{x₀}` and any family `𝒞` of such compressors,
`π(k_x) = π(k_y)` whenever `x, y` lie in one fiber of the `G`-equivariant
quotient `X → X/∼` generated by the moves; on a transitive orbit `G/Γ`
these fibers are the fibers of `G/Γ → G/J` with
`J = ⟨Γ, Γ↑_𝒞⟩` (block systems of a transitive action are exactly
intermediate subgroups).  The user draft's Theorem A is the transitive
case with a single `Λ = Γ`.

## 4. Factorization and the reduction of the MF radical

**Abelianization forcing** (kernel-checked as `commute_map_of_collapse`):
if `π(wkw⁻¹) = π(k)` and `wkw⁻¹` commutes with `k'`, then `π(k)` commutes
with `π(k')`.  In a collapsed fiber with two distinct points, taking `w`
moving `x` to `y ≠ x` in the fiber makes any two lamps at `x` commute in
the image.

**Theorem 3 (factorization and radical reduction).**  Setting of Theorem
2, `X = G/Γ` transitive, `J = ⟨Γ, Γ↑_𝒞⟩ ≠ Γ`, `Y = G/J`, `p : X → Y`.
Assume `K` is generated by its torsion elements.  Then every corona
representation of `W = K^{(X)} ⋊ G` factors through the canonical
`G`-equivariant quotient

```
q : K^{(X)} ⋊ G  →  K_ab^{(Y)} ⋊ G,      q(k_x) = k̄_{p(x)},  q|_G = id,
```

whose kernel is `{ f ∈ K^{(X)} : Π_{x ∈ p⁻¹(y)} f(x) ∈ [K,K] for every
y ∈ Y }` (fiberwise products taken in any order modulo `[K,K]`).
Consequently

```
ker q ≤ Rad_MF(W)     and     Rad_MF(W) = q⁻¹( Rad_MF(K_ab^{(Y)} ⋊ G) ).
```

If moreover the quotient `K_ab^{(Y)} ⋊ G` is MF (e.g. residually finite),
then **exactly**

```
Rad_MF(W) = ker q,
```

and the universal MF quotient of `W` is `K_ab^{(Y)} ⋊ G`.

Proof of the factorization from Theorems 1–2: torsion lamps collapse along
fibers; products of torsion elements then collapse (both sides are
products of collapsed factors), giving collapse for all of `K`; two
points per fiber (from `J ≠ Γ` and transitivity of `G` on fibers) force
fiberwise-abelian images; the universal property of the restricted
product over the abelian target assembles `q`.  The radical identities
are the kernel-checked reduction theorem
`actualCoronaMFResidual_eq_comap_quotient` plus the existing exact
criterion `actualCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF`.
The hypothesis-gated Lean endpoints packaging exactly this are
`torsionCollapseDefect_le_actualCoronaMFResidual` and
`actualCoronaMFResidual_eq_torsionCollapseDefect`.

Mixed case: if `K` is not torsion-generated, the same argument collapses
the subgroup `T(K)` generated by torsion, and `q` becomes the quotient
abelianizing-and-fusing only the `T(K)`-coordinates along fibers.

**Intrinsic form.**  Define the torsion compression-collapse defect
`N(W) = ⟨⟨ ⁅λ, k⁆ : (Λ,s,k) as in Theorem 1 (group-side witnesses) ⟩⟩`
(Lean: `torsionCollapseDefect`, per pair `(L, s)`).  Then
`N(W) ≤ Rad_MF(W)` and `Rad_MF(W) = q_N⁻¹(Rad_MF(W/N(W)))` — the analogue
of the manuscript's intrinsic compression radical, but with a possibly
**infinite** forced subgroup, versus the finite-normal scope of
`IntrinsicCompressionMFRadical`.

## 5. The doubling family: complete MF radicals

Take `Γ = ℤ³ ⋊ SL₃(ℤ)` (Kazhdan), the doubling `α(v,A) = (2v,A)`, and the
ascending HNN ambient

```
G = (ℤ[1/2]³ ⋊ SL₃(ℤ)) ⋊_α ℤ = ⟨Γ, t⟩,    tΓt⁻¹ = 2ℤ³ ⋊ SL₃(ℤ) ≤ Γ.
```

With compressors `𝒞 = {t^j : j ≥ 1}`: `Γ↑ = ∪_j t^{-j}Γt^j =
ℤ[1/2]³ ⋊ SL₃(ℤ) =: N ⊴ G`, `J = N`, `Y = G/N ≅ ℤ` via the height map
`ℓ`.  For **any finite** `K` and `W_K = K^{(G/Γ)} ⋊ G`:

```
Rad_MF(W_K) = ker( q_K : W_K → K_ab^{(ℤ)} ⋊ G ),
```

where the image of a lamp configuration `f` at height `r` is
`Π_{ℓ(x)=r} f(x)` in `K_ab`.  Proof of the missing (exactness) half:
the quotient is residually finite —

* `G` is RF: the faithful rational representation
  `(v,A,j) ↦ [[2^j A, v],[0,1]] ∈ GL₄(ℤ[1/2])` (injective since
  `det(2^jA) = 2^{3j} = 1` forces `j = 0`), reduced mod odd primes `p ∤ a`
  for a nonzero entry `a/2^r` of the matrix minus the identity;
* `K_ab^{(ℤ)} ⋊ G ↪ G × (K_ab wr ℤ)` via `(f,g) ↦ (g, (f, ℓ(g)))`
  (checked: the `G`-action on `K_ab^{(ℤ)}` factors through `ℓ`);
* `K_ab wr ℤ` is RF for finite abelian `K_ab` (separate the ℤ-coordinate
  by a congruence; separate a finitely supported lamp by a cyclic period
  keeping its support injective).  For infinite `K` the statement holds
  whenever `K_ab` is RF, by Gruenberg's wreath criterion (literature
  input; not used for the finite case).

Punchlines:

* `K = C₂`: `Rad_MF = { f : Σ_{ℓ(x)=r} f(x) ≡ 0 (mod 2) for all r }` —
  even Boolean parity on every height level; universal MF quotient
  `C₂^{(ℤ)} ⋊ G`, residually finite.
* `K = A₅` (or any nontrivial perfect finite group): `K_ab = 1`, so
  **every corona representation kills every lamp**:
  `Rad_MF(W_K) = K^{(G/Γ)}`, universal MF quotient `G` itself.  `W_{A₅}`
  is a finitely generated non-MF group whose complete MF radical is its
  entire locally finite lamp base.

Alignment with the repo: the literal `ℤ³⋊SL₃(ℤ)` presentation carries the
usual conditional-(T) caveat of the Literal surface; instantiating the same
doubling telescope at the in-repo unconditional Kazhdan base
(`ExplicitNonMFBase.Base` + `MappingTelescope⋊ℤ`) makes the *collapse* half
unconditional, with only the RF/MF property of the corresponding quotient
outstanding.

**Sofic byproduct.**  For the Kun--Thom pairs, the identical globalization
plus abelianization forcing runs on the sofic side (KT centralizer
normalization plays the role of Theorem 1; `k_Γ` is centralized by `Γ` as
a group element), strengthening `COMMUTING_WREATH_SOFIC_RADICAL.md` from
`C₂` to every finite lamp group `K`:
`Rad_sof(K^{(G/Γ)}⋊G) = ker(K^{(G/Γ)} → K_ab^{(G/N)})`-semidirect kernel,
with the same `G × (K_ab wr G/N)` RF witness.  In particular the sofic and
MF radical formulas have the same shape — fiberwise abelianized products —
each over its own class of pairs.

## 5½. Defect saturation (after Fournier-Facio)

Credit note.  Francesco Fournier-Facio suggested (personal communication,
2026-08-14) that the manuscript's affine Section 5 "can be replaced by a
suitable small cancellation argument, analogously to what I do here
[arXiv:2608.02025]".  The program sketched in this subsection is a
session-side development of that suggestion (GPT-5.6-assisted analysis on
the user's side; unrefereed; no priority claims): FF's idea is credited
for the small-cancellation route and for the construction of
arXiv:2608.02025; the amplification framing below is derived from it.

The principle: *detect a defect analytically; saturate it algebraically.*
The in-repo theorem `normalKazhdan_le_normMFResidual`
(`Sofic/NormalKazhdanMFRadical.lean`) already says: a normal Kazhdan
subgroup inside the compression defect lies in the MF radical.  If a
Hull/Osin small-cancellation quotient makes the defect **equal to the
whole group** (FF's torsion-free construction supplies exactly the right
compression configuration), the ambient (T) then gives the **full MF
radical**: `Rad_MF(G) = G`, i.e. every homomorphism to an MF group is
trivial, every nontrivial quotient is non-MF, the profinite and Bohr
completions are trivial, and (in the mixed form, combining with the
soficity criterion of arXiv:2608.02025) every nontrivial quotient is
simultaneously nonsofic and non-MF — an *approximation black hole*.

Lean status of this program: the plumbing is now **machine-checked and
unconditional** in `Sofic/DefectSaturation.lean` (with the credit note in
its module docstring): `involutiveCollapseDefect_le_ker_of_isCDEOperatorMF`
(the defect dies in every map to an operator-MF group — no saturation
needed), `actualCoronaMFResidual_eq_top_of_saturated` (saturated defect
⟹ full MF radical), `actualCoronaMFInvisible_of_saturated`,
`map_eq_one_of_saturated` (the approximation black hole), and
`not_isCDEOperatorMF_of_saturated`.  The *existence* input (the Hull
7.1/Osin small-cancellation quotient, acylindrical hyperbolicity,
suitable subgroups) remains a dedicated formalization program of its own
— tracked in Cairn (`defect-saturation-full-mf-radical`,
`mixed-approximation-black-hole`), nothing of it is assumed anywhere on
the trust surface.

## 6. What the reduction theorem means

`Rad_MF(W) = q⁻¹(Rad_MF(W/ker q))` upgrades the mechanism from a non-MF
*criterion* to a *computation of the universal MF quotient*: all corona
representation theory of `W` is that of the far smaller
`K_ab^{(Y)} ⋊ G`.  Conceptually:

> one-sided Kazhdan compression + finite spectrum
> ⟹ finite-dimensional models cannot resolve the extra orbit directions
> created by the inverse of the compression, and the failure is exactly
> the fiberwise abelianized fusion of the lamp algebra.

The Clifford sign of the manuscript and the Boolean two-lamp word of the
preliminary are two shadows of this one collapse.

## 7. Boundary of the mechanism

* **(T) is not weakenable to relative (T) of the compressed data.**  The
  Mautner/transport input fails already for the pair `(ℤ^d, 2ℤ^d)`: a
  mod-2 congruence character is fixed by `2ℤ^d` but not by `ℤ^d`, and
  arises in genuine finite-dimensional representations; there is no
  transport.  Consistently, the repo's cyclic-base calibration (Theorem C
  side: `BS(1,2)` base, amenable witness, MF by TWW) proves the
  *conclusion* fails without (T).  Both ends of the necessity are already
  in-repo; this document adds nothing conditional there.
* **Commuting orbits are essential to this proof.**  Anticommuting
  (Clifford) coordinates have no joint spectral labels and no rank metric;
  their collapse mechanism is the central sign one, which is genuinely
  different (it kills a central `C₂`, not a lamp base).  A common
  generalization ("commuting up to center") is open.
* **Torsion (of the image) is essential to this proof.**  Infinite
  spectrum destroys both the exact lifts and the integer-valued rank
  metric.  Whether torsion-free lamps can be collapsed is exactly the
  open torsion-free non-MF frontier (Cairn:
  `torsion-free-finitely-presented-non-mf`, locked by another session —
  not claimed here).
* **The trace scale tells a different story.**  At normalized trace the
  same wreath products can be sofic (the KT side computes a *sofic*
  radical of the same shape), so the collapse is a norm-corona phenomenon;
  the `k_n` rescaling is precisely what defeats trace/rank blindness, and
  the scaled transport theorem is what makes that rescaling legitimate.

## 8. Audit deltas against the user draft (2026-08-14)

All auditable steps of the draft check out; the changes are strict
generalizations or precision repairs:

1. **Pointwise, image-side hypotheses** (§1) replace the wreath setting:
   the G-set, transitivity, and the group-side torsion/commutation/
   centralization hypotheses are all shed; the draft's Theorems A and B
   become corollaries (§3, §4).
2. **The Mautner step is grounded.**  The draft asserted "the matricial
   Mautner lemma applies … even with the arbitrary scalar rescaling",
   citing the preliminary.  Audit finding: at general scales the
   finite-trace argument (equal trace + containment) is unavailable — the
   limit trace is only semifinite, and the fixed-space containment
   `K_ω^Λ ⊆ K_ω^H = σ(s)K_ω^Λ` has genuine unilateral-shift room in a
   plain Hilbert space.  What is true, and now kernel-checked, is the
   **mass-sector** statement (`scaled_transport*`): the repo's spectral
   capture + equal-rank-flip chain survives every rescaling once the
   op-norm bound on the commutant sequence is replaced by the mass bound,
   and every ultraproduct vector is mass-bounded.  The draft's appeal is
   thereby validated, with the precise sector hypothesis made explicit.
3. **The eventuality bookkeeping is repaired.**  The sequential transport
   statement quantifies cofinitely; membership in `K_ω^H` gives only
   `ω`-eventual hypotheses.  The finite-level chain is per-`n`, so the
   `ω`-version follows; the doc states this rather than passing silently
   from one to the other.
4. **FH usage is pinned — and turns out to be in-repo.**  Delorme's
   theorem is applied to the real Hilbert structure of the ultraproduct
   (completeness suffices; no separability is needed by the in-repo
   statement); (T) ⟹ finite generation is the third distinct use of (T).
   Contrary to the session's initial assessment, **both are already
   kernel-checked in-repo** (`Kazhdan/DelormeFixedPoint.lean`,
   `Kazhdan/KazhdanFiniteGeneration.lean`), so the analytic Theorem 1 is
   blocked only on formalization labor (ultraproduct packaging, lifts,
   the rank-metric cocycle layer), not on any classical input.  Until
   that labor is done it remains hypothesis-gated in the endpoint
   theorems.
5. **The C_m lift step the user flagged as fragile is fine**: the only
   points needing care were (a) inductive commuting lifts (averaging +
   spectral cut), (b) the per-`λ` finite exceptional-set fix-up done
   coordinate-by-coordinate (bad `(λ,n)` pairs set to the trivial
   partition, preserving global commutation), (c) rigidity of exact
   lifts.  All three are recorded in Step 1.
6. **Radical formalism**: the draft's `Rad_MF = q⁻¹(Rad_MF(quotient))`
   is now the kernel-checked `actualCoronaMFResidual_eq_comap_quotient`;
   the exactness criterion was already in-repo.
7. **New**: the sofic byproduct (§5), the intrinsic defect subgroup and
   its conditional endpoints, the mixed non-torsion-generated statement,
   the multi-`Λ` and iterated-closure globalization, and the boundary map
   (§7).

## 9. Formalization state and inputs

Kernel-checked, unconditional (this session; modules imported by the root):

* `Sofic/ScaledKazhdanTransport.lean` — Frobenius-mass calculus
  (`matMass_*`), scaled vanishing/boundedness kits, scaled capture
  (`scaled_capture_vanishing`), and the scaled transport theorems
  (`scaled_transport`, `scaled_transport_star`, `scaled_transport_both`,
  `compressionSet_*`, `compressionGroup_le_scaledCommutantStabilizer`,
  `compressionGroup_scaled_transport_both`), with the bridges
  (`scaledMassVanishing_card_iff_hsSqVanishing`,
  `IsUniformlyBounded.isScaledMassBounded_card`) showing the dimension
  scale is the special case.
* `Sofic/TorsionCompressionCollapse.lean` — `piConjStabilizer`,
  expansion propagation (`expansionSubgroup_le_piConjStabilizer`),
  abelianization forcing (`commute_map_of_collapse`), the reduction
  theorem (`actualCoronaMFResidual_eq_comap_quotient`), the witness
  predicate (`IsTorsionCompressionWitness`, satisfiable), the defect
  subgroup (`torsionCollapseDefect`), and the hypothesis-gated endpoints
  (`torsionCollapseDefect_le_actualCoronaMFResidual`,
  `actualCoronaMFResidual_eq_torsionCollapseDefect`).

* **The unconditional involutive collapse (this session's summit).**  The
  full analytic Theorem 1, for the involutive lamp class `k² = 1`, is now
  machine-checked end to end with **no hypotheses beyond group theory**:

  - `Sofic/InvolutionRankMass.lean`, `Sofic/ExactInvolutionLifts.lean` —
    rank/mass calculus (`matMass_sub_eq_four_mul_rank`,
    `matMass_le_rank_mul_sq_opNorm`, `rank_eq_of_projections_close`) and
    exact commuting involution lifts
    (`exists_isExactInvolution_comm_of_unitary`, `δ(ε) = ε`).
  - `Kazhdan/UltralimitGaussianBoundedness.lean`,
    `Kazhdan/ApproximateCircumcenter.lean`,
    `Kazhdan/UltralimitGeometry.lean` — Shalom-style hyperreal
    standard-part calculus: Gaussian positive-definiteness ⟹ bounded
    displacement profile (`profile_bounded_of_isKazhdanPair`, consuming
    the in-repo Delorme theorem), sequence-level circumcenters
    (`exists_near_center`, `seqNormSq_sub_le_of_near_center`).
  - `Sofic/InvolutionMicrostateTools.lean`,
    `Sofic/InvolutionOrbitMicrostates.lean` — flattening isometry, the
    rigidity of commuting exact involutions (distance `< 2` ⟹ equal),
    and diagonal extraction of corrected involution microstates
    (`exists_involutionMicrostates`).
  - `Sofic/InvolutionCollapse{Metric,Profile,Cocycle,Center,IndexCapture}
    .lean` — the rank displacement metric `dV`, normalized displacement
    vectors `bVec` with the exact mass anchor
    (`sum_normSq_bVec_eq_four`), marked positivity
    (`eventually_one_le_kNorm_of_marked`), the stagewise coboundary
    defect (`eventually_coboundary_defect_small`), the Guichardet
    circumcenter primitive (`exists_approximate_coboundary`), and the
    per-index spectral capture (`index_capture`).
  - `Sofic/InvolutionCollapseEndpoint(Prep).lean` — the assembly:
    `no_marked_model` (no marked almost representation separates the
    collapse commutator), `actualCoronaMFInvisible_commutator` (every
    corona representation kills `⁅ι(γ₀), k⁆`), and the **discharged**
    endpoints for the involutive witness class:
    `actualCoronaMFInvisible_of_involutiveWitness`,
    `involutiveCollapseDefect_le_actualCoronaMFResidual` (radical
    membership, unconditional),
    `actualCoronaMFResidual_eq_comap_involutive_quotient` (radical
    reduction, unconditional), and
    `actualCoronaMFResidual_eq_involutiveCollapseDefect` (exactness; the
    only remaining hypothesis is the intrinsic one, MF-ness of the defect
    quotient — the exactness *direction*, not the collapse).

Status of the general-`m` witness class: the endpoints
(`torsionCollapseDefect_le_actualCoronaMFResidual`,
`actualCoronaMFResidual_eq_torsionCollapseDefect`) remain reductions
gated on the collapse hypothesis for `m > 2`; the involutive class
(`m = 2`, which contains the `K = A₅`-generated applications via the
involutions of `A₅`) is fully discharged as above.  No `sorry`, no
axioms, no literature inputs anywhere on this chain: Delorme and Kazhdan
finite generation are the in-repo theorems.

Inputs of Theorem 1 and their status:

1. Delorme ((T) ⟹ FH): **kernel-checked in-repo** and now consumed by
   the collapse chain through `profile_bounded_of_isKazhdanPair`.
2. Kazhdan finite generation: **kernel-checked in-repo**, consumed
   through `exists_symmetric_generating_pair`.
3. Commuting involution lifting from a norm matrix corona:
   **kernel-checked this session** (`ExactInvolutionLifts` +
   `InvolutionOrbitMicrostates`); the general finite-order commuting
   lifting remains open and gates only the `m > 2` class.
4. Gruenberg's wreath RF criterion — a literature input used **only** for
   infinite `K` in §5; the finite case is self-contained.

Remaining formalization ladder, in order of value: (i) finite-order
(`m > 2`) commuting lifts, which would upgrade the general witness class
to unconditional; (ii) the wreath instantiation and the doubling
family's RF quotient (`GL₄(ℤ[1/2])` congruence reductions —
`IntegralLinearResiduallyFinite` is the ℤ-precedent); (iii) the
FF-inspired saturation plumbing of §5½ (defect normal closure `= ⊤` plus
ambient `(T)` ⟹ full MF radical, via `normalKazhdan_le_normMFResidual`).

## 10. Manuscript promotion (2026-08-15)

The involutive branch of this program is now printed in
`non_mf_groups_exist.tex`: `subsec:collapse` ("Orbit collapse and defect
saturation") states `def:invwitness`, `thm:collapse` (with a printed
six-step proof following the formal ladder), `cor:collapsequot`,
`thm:saturation` (with the Fournier-Facio credit and the explicit
non-assumption of Hull/Osin), and `cor:pullback` (the unconditional
radical reduction) in §11.1.  The abstract obstruction over an invisible
subgroup is `thm:abstract-nk` with the new module
`Sofic/NormalKazhdanHyperlinearKilled.lean` (the property-(T) companion
of `finiteNormal_le_normMFResidual_of_hyperlinear_killed`; pushforward
along range restriction = `OpAlmostRepresentation.comap`), which also
supplies the previously missing normal-Kazhdan endpoints over the
intrinsic defect `𝔇(H,L)` (`cor:intrinsic-nk` and its part form).  The
general `m > 2` collapse remains gated on exact commuting
finite-spectrum lifts, and the manuscript says so
(`rem:collapse-finite-stage`).
