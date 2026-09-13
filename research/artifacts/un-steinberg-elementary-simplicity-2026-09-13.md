# Uniform simplicity of elementary groups over Steinberg algebras

Lane `un-simplicity` (UN swarm), 2026-09-13. Status: written proofs, **unreviewed**. The ring criterion of §3 is
certified in Lean on main (`GroupApproximation/Pestov91/SimpleModCentre.lean`, root-imported); §§1, 2 and 4 are
paper proofs.

## 0. Statements

Let `k` be a nonzero commutative ring and `𝒢` an ample groupoid (étale, totally disconnected unit space) with compact
unit space `𝒢⁽⁰⁾`. `A_k(𝒢)` is its Steinberg algebra: the span of indicators `χ_B` of compact open bisections, with
`χ_B χ_C = χ_(BC)`. It is unital with `1 = χ_(𝒢⁽⁰⁾)`.

- **Theorem S1 (local annihilation).** If `𝒢⁽⁰⁾` is infinite, then `A_k(𝒢)` has *local annihilation*: for every finite
  `F ⊆ A_k(𝒢)`, the set `S_F = {s : ∃ t ≠ 0, ts = 0 and tfs = 0 for all f ∈ F}` generates `A_k(𝒢)` as a non-unital
  ring. In fact `S_F` already contains a family `χ_(V_i) A_k(𝒢)` with `V_1, …, V_r` a clopen partition of `𝒢⁽⁰⁾`.
- **Theorem S2 (scalar centre).** If `k` is a field, `𝒢` is Hausdorff, effective and minimal, then `Z(A_k(𝒢)) = k·1`.
- **Theorem S3 (ring criterion; Lean).** Let `R` be a unital simple ring with local annihilation, and `n ≥ 3`. Then
  every normal subgroup of `EL_n(R)` is central or all of `EL_n(R)`, so `EL_n(R)/Z(EL_n(R))` is simple.
- **Theorem S4 (uniform simplicity).** Let `k` be a field and `𝒢` a Hausdorff ample groupoid with compact infinite unit
  space that is minimal and effective. Put `R = A_k(𝒢)` and `n ≥ 3`. Then:
  - every normal subgroup of `EL_n(R)` is central or everything, and `Z(EL_n(R)) ⊆ k^× I_n`;
  - `S_n = EL_n(R)/Z(EL_n(R))` is an infinite simple group;
  - if `k` is finite and `R` is finitely generated as a ring, `S_n` is an infinite finitely generated simple group with
    property (T).

## 1. Proof of S1

**Restriction identity.** For compact open `U, W ⊆ 𝒢⁽⁰⁾` and `f ∈ A_k(𝒢)`, `χ_W f χ_U` is `f` multiplied by the
indicator of `{g : r(g) ∈ W, s(g) ∈ U}`. This is convolution with unit-space indicators: `(χ_W f)(g) = χ_W(r g) f(g)`
and `(f χ_U)(g) = f(g) χ_U(s g)`.

Fix a finite `F`. Each `f ∈ F` is a finite combination of `χ_B` over compact open bisections, so all of `F` is
supported in `K = B_1 ∪ … ∪ B_m`, finitely many compact open bisections. Write `α_j : s(B_j) → r(B_j)` for the
homeomorphism `s(g) ↦ r(g)`, `g ∈ B_j`; each `s(B_j)` is clopen.

Fix `x ∈ 𝒢⁽⁰⁾`, and let `P_x = {x} ∪ {α_j(x) : x ∈ s(B_j)}`, a finite set. Since `𝒢⁽⁰⁾` is infinite, pick
`y ∉ P_x` and a clopen `W ∋ y` disjoint from `P_x`, which is possible because `𝒢⁽⁰⁾` is Hausdorff and totally
disconnected. Choose a clopen `V_x ∋ x` such that:
- `V_x ∩ W = ∅`, possible since `x ∉ W`;
- for each `j` with `x ∈ s(B_j)`: `V_x ⊆ s(B_j)` and `α_j(V_x) ∩ W = ∅`, possible by continuity of `α_j` at `x`,
  since `α_j(x) ∉ W` and `W` is clopen;
- for each `j` with `x ∉ s(B_j)`: `V_x ∩ s(B_j) = ∅`, possible since `s(B_j)` is clopen.

These properties pass to every clopen `V ⊆ V_x`. For such `V` and every `a ∈ A_k(𝒢)`, put `s = χ_V a` and `t = χ_W`:
- `t ≠ 0` since `W ≠ ∅`;
- `ts = χ_(W ∩ V) a = 0`;
- `tfs = (χ_W f χ_V) a`. An arrow `g ∈ K` with `s(g) ∈ V` lies in some `B_j` with `x ∈ s(B_j)`, so
  `r(g) = α_j(s g) ∈ α_j(V_x)`, which misses `W`. By the restriction identity `χ_W f χ_V = 0`.

So `χ_V A_k(𝒢) ⊆ S_F`. By compactness finitely many `V_(x_1), …, V_(x_r)` cover `𝒢⁽⁰⁾`; refine them to a clopen partition
`V_1, …, V_r` with `V_i ⊆ V_(x_i)`. Then `a = Σ_i χ_(V_i) a` for every `a`, so the additive closure of `S_F` is
`A_k(𝒢)`. ∎

Only compactness, total disconnectedness and infiniteness of the unit space are used, and the étale structure through
`α_j`. Hausdorffness of `𝒢`, minimality and effectiveness are not.

## 2. Proof of S2

Let `z ∈ Z(A_k(𝒢))`, a locally constant function with compact support.
- **Supported on isotropy.** For clopen `U ⊆ 𝒢⁽⁰⁾`, `z χ_U = χ_U z`, so `χ_(𝒢⁽⁰⁾∖U) z χ_U = χ_(𝒢⁽⁰⁾∖U) χ_U z = 0`. So `z`
  vanishes on arrows `g` with `s(g) ∈ U` and `r(g) ∉ U`. Clopen sets separate points of `𝒢⁽⁰⁾`, so `z(g) ≠ 0` forces
  `r(g) = s(g)`. The support of `z` is open (`z` is locally constant), so it lies in the interior of the isotropy,
  which is `𝒢⁽⁰⁾` by effectiveness. So `z ∈ LC(𝒢⁽⁰⁾, k)`.
- **Invariant.** For a compact open bisection `B`, `χ_B z = z χ_B` reads `z(r g) = z(s g)` for `g ∈ B`. So `z` is
  constant on orbits.
- **Constant.** `z` is continuous and constant on each dense orbit, so `z` is constant. ∎

## 3. Theorem S3 (Lean-certified on main)

`GroupApproximation.Pestov91.isSimpleGroup_elementaryGroup_quotient_center` (`SimpleModCentre.lean`): for `|ι| ≥ 3`,
`[IsSimpleRing R]` and `LocalAnnihilation R`, `IsSimpleGroup (EL_ι(R) ⧸ center)`. `LocalAnnihilation R` is literally
S1's property:
`∀ F : Finset R, NonUnitalSubring.closure {s | ∃ t, t ≠ 0 ∧ t*s = 0 ∧ ∀ f ∈ F, t*f*s = 0} = ⊤`.

Paper proof, following the module docstring:
1. Let `N ⊴ EL_n(R)` be noncentral and `g ∈ N` noncentral. The coefficients `s` whose roots `e_ij(s)` all commute
   with `g` form a non-unital subring. Applying local annihilation to the entries of `g`, some `s ∈ S_F` gives a root
   `h = e_ij(s)` not commuting with `g`, with `t ≠ 0`, `ts = 0` and `t g_pk s = 0`.
2. `ρ = g h g^(-1) h^(-1) ∈ N`, `ρ ≠ 1`, and `t(ρ − 1) = 0` entrywise.
3. Simplicity of `R` gives `c` with `(ρ − 1)_(qm) c t ≠ 0`. The commutator of `ρ` with `e_ml(ct)` is the one-column
   matrix `1 + (ρ−1) e_ml(ct)`, and column extraction gives a nonzero root in `N`.
4. The level `{a : e_pq(a) ∈ N for all p ≠ q}` is a nonzero two-sided ideal, hence `R`, so `N = EL_n(R)`.

**Centre.** A central `g ∈ EL_n(R)` commutes with every `e_ij(1)`, so `g = λI`; commuting with `e_ij(a)` gives
`λ ∈ Z(R)^×`. So `Z(EL_n(R)) ⊆ Z(R)^× I_n`.

## 4. Assembly of S4

- `R = A_k(𝒢)` is simple, by the simplicity theorem for Steinberg algebras over a field: Hausdorff ample, effective
  and minimal (import node `steinberg-algebra-simple-iff-minimal-effective`).
- It has local annihilation by S1, so S3 applies.
- By S2 and §3, `Z(EL_n(R)) ⊆ k^× I_n`.
- `S_n` is infinite: `R` is infinite-dimensional (infinitely many disjoint clopens), and `e_12(a) e_12(b)^(-1)` central
  forces `a = b`.
- For finite `k` and finitely generated `R`, `EL_n(R)` has (T) (`elementary-groups-over-fg-rings-have-property-t`,
  Ershov–Jaikin-Zapirain). (T) passes to quotients, and a (T) group is finitely generated.

## 5. Calibration and scope

- **Pestov 9.1.** `LC(X, F_q) ⋊ Z = A_(F_q)(Z ⋉ X)` for an infinite minimal subshift (free, minimal, effective). S4
  recovers the simplicity part of the answer. The Lean witness already goes through S3, via
  `localAnnihilation_of_crossedProduct`.
- **Free minimal Z^d-subshifts.** S4 gives the simplicity half of `free-minimal-subshift-elementary-groups-are-simple-kazhdan`
  with no box towers.
- **Leavitt.** `L_k(1,d) = A_k(𝒢_d)`, where `𝒢_d` is the Cuntz groupoid on `{1,…,d}^N`: Hausdorff, ample, minimal,
  effective, Cantor unit space. S4 gives simplicity of `EL_n(L_k(1,d))/Z` for all `n ≥ 3` and every field `k`, with no
  exchange-ring input. The tex proof of simplicity of `L_(F_2)(1,2)^× = EL_4(R)` uses Preusser's sandwich theorem for
  exchange rings.
- **Further minimal effective ample groupoids** with finitely generated Steinberg algebras also give infinite finitely
  generated simple Kazhdan groups: Katsura–Exel–Pardo, Nekrashevych groupoids of self-similar actions, minimal Z^d- or
  group-action transformation groupoids, higher-rank graphs satisfying the aperiodicity and cofinality conditions.
  Finite generation must be checked case by case.
- **Model tests.**
  - A field `k`: `S_F = {0}`, so local annihilation fails, as it should; S3 is not the source of `PSL_n(k)` simplicity.
  - `LC(X, k)` for Cantor `X`: local annihilation holds by S1, but the ring is not simple, and `EL_n` has congruence
    normal subgroups. So S3 needs both hypotheses.
  - The pair groupoid on `d` points (`R = M_d(k)`): finite unit space, so S1 does not apply.
  - Non-effective `𝒢`, e.g. a trivial Z/2 isotropy bundle: the centre is larger and the ring is not simple. S2 and S4
    need effectiveness.

## 6. Credits and novelty bound

- Steinberg algebras and their simplicity: Steinberg; Clark–Farthing–Sims–Tomforde; Brown–Clark–Farthing–Sims
  (complex case); the field versions are cited in the import node.
- Property (T): Ershov–Jaikin-Zapirain.
- S3 and its Lean proof are the repository's (fz swarm, `SimpleModCentre.lean`).
- S1 and S2 are elementary; S2 is the effective and minimal case of the standard description of the centre as class
  functions on the interior of the isotropy.
- **Bounded check.** I have not verified whether the local-annihilation criterion, or simplicity of `EL_n` modulo
  centre over arbitrary simple rings, already appears in the normal-subgroup literature. Sandwich theorems are known for
  quasi-finite rings (Vaserstein, Golubchik) and exchange rings (Preusser, LMA 70 (2022)). un-prior-art owns that
  search.
