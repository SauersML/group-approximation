# Swarm notes: `penrose-derived-full-group-is-finitely-presented` (2026-09-16)

Agent: `swarm-penrose-derived-full-group-is-`. Locked holes:
`penrose-derived-full-group-is-finitely-presented` and its negation
`penrose-derived-full-group-is-not-finitely-presented`. Both are unlocked at the end.

## 1. Setup

- `𝒫` is the Penrose tiling group of Chornyi--Juschenko--Nekrashevych (ChJN,
  arXiv:1602.04255). By `penrose-tiling-group-is-an-amenable-orbit-full-group`,
  `𝒫 ≅ [[Lambda ~ X]]`, where `Lambda = P/Lat ≅ Z^2 ⊕ Z/5` acts freely on the cut torus
  `X = C~/Lat` with an invariant measure of full support. `D(𝒫)` is finitely generated,
  infinite, simple and sofic.
- **Target.** Is `D(𝒫)` finitely presented? Both the claim and its negation are OPEN.
- **Recorded obstructions and methods before this session.**
  - Homology is finitely generated (`penrose-derived-full-group-homology-is-finitely-generated`).
  - Additive relation invariants are dead.
  - Compression methods need compressible clopen sets, which the invariant measure forbids.
  - **Finite presentation forces finite type** (`fp-alternating-full-groups-of-free-subshifts-force-sft`,
    Theorem G). It was listed as "expected dead" with two unchecked points:
    - adapting it to `Lambda`;
    - whether `Lambda ~ X` is conjugate to a `Lambda`-SFT.
- **Plan.** Settle the unchecked finite-type question, since it is the only recorded
  obstruction that could still fire. Then check whether the other LEF-type obstruction,
  rational polytope exchanges, can apply to the torus model.

## 2. Literature gate (2026-09-16, arXiv API; abstracts read, TeX read where stated)

- **ChJN, arXiv:1602.04255.** TeX source `IET_copy.tex` fetched from arXiv and read on
  2026-09-16.
  - Line 95: amenability of `𝒫` is open.
  - No statement on finite presentation of `D(𝒫)`.
  - The imports used below are at lines 299--315, 336--358, 464--467, 485--500, 512--527
    and 569--582. These line numbers differ slightly, beyond line 95, from the copy cited in
    `penrose-tiling-group-amenable-orbit-citation`.
- **Kuang, "Near full groups of bounded type: full group completion", arXiv:2607.25729**
  (2026-07-28). Abstract: as an application, a fragmentation group of the modified LMS
  group of the Penrose tiling equals its topological full group. No finite presentation
  result.
- **Nekrashevych, "Semigroups, groups, and algebras of dynamical origin", arXiv:2509.05524**
  (2025-09-05). Survey. The expert heuristic that full groups of shift-invariant groupoids
  are rarely finitely presented is already recorded in the target node. No result on
  `D(𝒫)`.
- **Fernique--Lutfalla, "Geometrical Penrose Tilings are characterized by their 1-atlas",
  arXiv:2211.08239** (2022-11-15). Abstract: decorated rhombus Penrose tilings form a
  tiling space of finite type. Undecorated ("geometrical") ones are characterized by a
  vertex atlas, which "though considered as folk" had no published complete proof. This is
  the tiling-space statement; it says nothing about ChJN's `Lambda`-action.
- **Garrido--Reid, "Locally compact piecewise full groups of homeomorphisms",
  arXiv:2501.00908** (2025-01-01). Checked; not relevant to finite presentation here.
- **De Bruijn, "Algebraic theory of Penrose's non-periodic tilings of the plane" I, II
  (1981).** Cited by ChJN for `V' ≅ 𝒯`. Not fetched: **unverified**.
- **Conclusion of the gate.** No source found that proves or refutes finite presentation of
  `D(𝒫)`, and none that states finite type for ChJN's `Lambda`-coding. The target stays
  open.

## 3. What was proven

### 3.1 The cut-torus subshift is of finite type

New claim `penrose-cut-torus-subshift-is-of-finite-type`, route
`penrose-cut-torus-subshift-finite-type-proof`, full proof in
`research/artifacts/penrose-cut-torus-sft-2026-09-16.md`.

**Theorem.** `Lambda ~ X` is expansive, and its coding `Y ⊆ A^Lambda` is a free minimal
subshift of finite type.

**Proof outline.**
1. **Lemma 0.** The decorated tile-patch topology on `𝒯` is compact and refines ChJN's
   Hausdorff vertex-patch topology, so they agree and patches are locally constant.
2. **Lemma 1.** `Θ : X -> 𝒯` is the composite of ChJN's homeomorphisms. The formula
   `ψ_x(λ) = s(f_λ) - s(f) + σ^(-1)(η(f_λ) - η(f))` gives a bijection `Lambda -> V(Θ(x))`
   with `Θ(x + λ) = Θ(x) - ψ_x(λ)`. It is a cocycle and locally constant in `x`. The key
   input is ChJN's translation rule `T_{ξ~ + v} = T_ξ~ - σ^(-1)(v)`.
3. **Coding.** `y_x(μ) = pat_{r_0}(Θ(x + μ))`, with `r_0` large enough that the increments
   `ψ_x(s)` and the inverse increments `ψ_x^(-1)(e)`, `e` a unit edge, are read off the
   patch.
4. **Finite type.** Take a colouring `y` all of whose `B(N)`-windows are legal.
   - Integrate increments to positions.
   - Read labelled rhombi from the patches. Lemma 3 identifies them near each label with a
     genuine tiling.
   - Glue them into a space `K`. `dev : K -> C` is a local homeomorphism with uniform
     sections, `K` is Hausdorff and connected, so `dev` is a covering and hence a
     homeomorphism.
   - The rhombi form a Penrose tiling `T`, and `y = y_{Θ^(-1)(T)}`.
   - Constants: `m_* = 2M(max(D, r_0 + 2)) + 2` and `N = max(L, (m_* + 2) D')`, where
     `M(r) = ⌈22 (r + 2)^2⌉` bounds edge distance.

**Consequence.** Theorem G is stated over every infinite finitely generated group,
`Z^2 ⊕ Z/5` included. Its conclusion, that `Y` is of finite type, holds. So no finite-type
argument can show that `D(𝒫)` is not finitely presented. This settles both "not verified"
items in the Theorem G entry of the negation node's Attempts, and the finite-type question
in the target node's Attempts ("Obstructions through finite models").

### 3.2 Irrational facet directions (Proposition 6 of the artifact)

**Proposition.** For every 2-dimensional `Q`-subspace `W ⊂ Q(ζ)`, one of the five
directions `iζ^j R` meets `W` only in `0`.

**Proof.** Put `u = ζ - ζ^4`, so that `Q(ζ) ∩ iζ^j R = ζ^j u Q(√5)`.
- If the directions `j = 0, 1` meet `W`, then `W = Q u(p + q√5) + Q ζu(r + s√5)`.
- The directions `j = 2, 3, 4` meet `W` if and only if the determinants
  `10(pr + ps - qr - 5qs)`, `-20(ps - qr)` and `-10(pr - ps + qr - 5qs)` vanish. These
  were computed exactly with sympy in
  `experiments/penrose-rational-directions-2026-09-16/allrational.py`.
- All three vanish only if `ps = qr` and `pr = 5qs`, which forces `(p/q)^2 = 5` or a zero
  generator. ∎

**For ChJN's lattice.** `rational_dirs.py` shows that the directions `j = 0, 1` are
rational and `j = 2, 3, 4` are not.

**Consequence.** `fp-simple-groups-have-no-rational-polytope-exchange-action` needs integer
facet normals. It cannot be applied to the natural torus models `C/Lat'` with
`Lat' ⊂ Q(ζ)`. Other, non-toral models are not excluded.

## 4. Approaches and exactly where each dies

1. **Negation through finite type (Theorem G).** Dies at its own hypothesis check. The
   conclusion "`Y` is of finite type" is true (§3.1). This is now a theorem, not the
   heuristic "matching rules are local".
   - The recorded heuristic was not enough on its own. `Lambda` is not a translation group
     of any tiling, so ChJN's definition of Penrose tilings by edge matching does not by
     itself give finite type of the `Lambda`-subshift.
   - The missing step was developing a colouring with legal windows into a plane tiling.
     That is Step 4 of the artifact.
2. **Negation through rational polytope exchanges / LEF.** Dies at Proposition 6.
   - Every torus model `C/Lat'` with `Lat' ⊂ Q(ζ)` has a facet direction that is
     irrational for `Lat'`.
   - So the rational specialisation of `rational-polytope-exchange-groups-are-lef` has no
     rational model to act on.
   - An irrational-direction LEF argument would have to control the phason slivers that
     appear in rational approximants.
3. **Negation through periodic approximants.** Dies at freeness plus finite type.
   - Let `Lambda' ≤ Lambda` have finite index, and let `N_0` be the finite-type window of
     §3.1.
   - A `Lambda'`-periodic colouring whose `B(N_0)`-windows are legal lies in `Y`, and would
     be a periodic point there. `Lambda` acts freely, so there are none.
   - Any LEF argument must therefore use colourings with illegal windows, the "relator
     shifts" of `zd-subshift-full-group-lef-via-periodic-relator-shifts`.
   - For Labbé, `research/artifacts/labbe-lef-2026-09-12.md` §4 records that every
     rational perturbation creates slivers. Whether a model can be exact over them is left
     open there (`labbe-shift-derived-full-group-is-lef`).
   - Nothing Penrose-specific was attempted beyond this observation.
4. **Negation through homology.** Already dead: every `H_j(D(𝒫))` is finitely generated.
   The Bieri--Eckmann `FP_2` criterion with nontrivial coefficients was not attempted.
5. **Positive side, through compression methods** (Matui, Li, contracting groupoids). Dead:
   they need compressible clopen sets, and the invariant measure of full support forbids
   them. This was already recorded.
6. **Positive side, through transfer from Labbé.** No transfer is available: finite
   presentation of `D([[Z^2 ~ Omega_U]])` is itself open
   (`labbe-shift-derived-full-group-is-finitely-presented`).
   - §3.1 shows only that the two problems lie in the same structural class: free minimal
     SFTs over one-ended finitely generated abelian groups, with an invariant measure.
   - A proof for one would need a method that uses more than finite type.

## 5. Status after this session

- Target `penrose-derived-full-group-is-finitely-presented`: **OPEN.**
- Negation `penrose-derived-full-group-is-not-finitely-presented`: **OPEN.**
- Every obstruction recorded in the graph is now known not to apply: finite type, rational
  polytope exchanges, periodic approximation, homology and additive relation invariants.
  Refuting finite presentation needs an invariant that sees more than the finite type of the
  subshift.
- **Suggested node updates** (not made here, because existing committed nodes were left
  untouched):
  - In `penrose-derived-full-group-is-not-finitely-presented`, the Theorem G entry could be
    marked dead by `penrose-cut-torus-subshift-is-of-finite-type`, with both "not verified"
    items resolved.
  - In `penrose-derived-full-group-is-finitely-presented`, "Obstructions through finite
    models" could cite the new claim for the finite-type question.

## 6. Open questions worth a hole

- Is `[[Lambda ~ Y]]` LEF, or is some finitely generated subgroup not LEF? Periodic
  relator shifts over `Z^2 ⊕ Z/5` would have to be built from pentagrid approximants with
  defects.
- Does `D(𝒫)` satisfy the Bieri--Eckmann `FP_2` criterion with coefficients in
  `Z[𝒫]`-modules not pulled back from abelian covers?

## 7. Weakest steps (for the referee)

1. **(I3a).** ChJN's unproved assertion that `𝒯` is a Cantor set in the vertex-patch
   topology, used as "a Penrose tiling is determined by its vertex set". It is checked on
   the pentagrid for regular `ξ~` only, without arrows (artifact §6.1).
2. **Step 4 of the artifact.** The point-set topology of the glued space `K`, and the
   bookkeeping that every chart use stays within `m_*`.
3. **(I3).** `V' ≅ 𝒯` as a homeomorphism, attributed by ChJN to de Bruijn. It is unverified
   here.

## 8. Files

- `research/penrose-cut-torus-subshift-is-of-finite-type.md` (claim)
- `research/penrose-cut-torus-subshift-finite-type-proof.md` (route; requires
  `penrose-tiling-group-is-an-amenable-orbit-full-group`)
- `research/artifacts/penrose-cut-torus-sft-2026-09-16.md` (full proof)
- `experiments/penrose-rational-directions-2026-09-16/{rational_dirs.py, rational_dirs.out, allrational.py, allrational.out}`
