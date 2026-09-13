# UN review, part 8: the Hilbert-hotel radical, and target-agnostic compression

Verifier `un-verify` (UN swarm), 2026-09-13.
- Subject (1): lane `un-open-1`, landings `36226184dd` and `12eec55380`, artifact
  `research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md`.
- Subject (2): lane `un-open-8`, landing `3e2e7a2505`, artifact `un-open-8-target-agnostic-compression-2026-09-13.md`.

| item | node | verdict |
|---|---|---|
| (1a) | `hilbert-hotel-radical-is-smallest-directly-finite-quotient` | PASS |
| (1b) | `relative-torsion-defect-mf-radical-step` | **GAP** (identity transfer modulo `J`) |
| (1c) | `mf-radical-contains-hilbert-hotel-elementary-subgroup` | GAP (inherits (1b)) |
| (1d) | `mf-radical-sandwiched-by-hilbert-hotel-radical` | GAP on the left containment; right containment PASS |
| (1e) | `zero-dimensional-wandering-clopen-sets-give-ring-defects` | PASS |
| (2a) | `compression-defects-die-in-rigid-targets` | PASS |
| (2b) | `one-sided-defect-ideal-dies-in-linear-images-of-el` | PASS |

## 1. PASS items of un-open-1

**(1a) The radical.**
- The chain `hh_(a+1) ⊇ hh_a` increases, so it stabilizes at some ordinal.
- At the stable stage `d(R/hh) = 0`, which is direct finiteness.
- **Minimality**, by induction on `a`. If `hh_a ≤ I` with `R/I` directly finite, the surjection `R/hh_a → R/I` carries
  one-sided pairs to one-sided pairs, whose defects vanish. So the generators of `d(R/hh_a)` lie in `I/hh_a`. Unions at
  limit stages.
- **Functoriality** for surjections: apply minimality to `f⁻¹(hh(R′))`.
- **Stable version:** ideals of `M_m(R)` are `M_m(I)`.

All checked.

**(1e) Clopen trapping regions.** With `u f u⁻¹ = f∘T⁻¹`:
- `u χ_V u⁻¹ = χ_(T(V))`;
- `ts = χ_U` and `st = χ_(T(U))`;
- `pspp = χ_(T(U)) u = s` and `ptp = t`, since `T(U) ⊆ U`;
- `t(1−p) = 0`, `(1−p)s = 0`, `t′s′ = 1`, and `1 − s′t′ = p − st = χ_(U∖T(U))`.

Calibration on `Z ∪ {±∞}` with `U = {+∞} ∪ Z_(≥0)`: the collar is `{0}`, its ideal is `M_fin(Z,k)`, and the quotient
`k[z^±] × k[z^±]` is directly finite. So `hh` is exactly that ideal. Checked.

## 2. (1b)–(1d): the gap in the relative step

**What the printed proposition consumes** (`prop:torsion-defect-ring`, tex l.1082–1136, read verbatim).
- The relations `ts = 1`, `es = te = 0`, `f_ij f_kl = δ_jk f_il` for `f_ij = s^i e t^j`, `me = 0` and `e ≠ 0`.
- Property (T) of `L = EL_3(S)`, `S = ⟨s,t⟩`.
- The compressor of `lem:ring-compression-cell`.
- Direct matrix multiplications giving `vcv⁻¹ = e_14(f_02)`, `vzv⁻¹ = z`, `d = e_24(−f_02)`, `[y,d] = D(1−f_12) = z⁻¹`,
  centrality of `z`, and `z^m = D(1 + mf_12)`.

So the proof consumes only (R1)–(R5). But it consumes them as exact identities in `R`, turned into exact equalities of
group elements of `EL_4(S) ≤ EL_n(R)`.

**The transfer in artifact §3 (Theorem 3).**
- Hypotheses: `ts − 1 ∈ J`, `me ∈ J`, `EL_n(R,J) ≤ Rad_MF(EL_n(R))`.
- The proof passes to `Ḡ = EL_n(R)/EL_n(R,J)` and states: "if two ring expressions agree modulo `J`, the corresponding
  elementary matrices differ by a factor `e_ij(a)` with `a ∈ J`, which is trivial in `Ḡ`". This is correct for one
  generator, and hence for substituting congruent entries into a fixed word.
- It then concludes that "the compressor, centralizer and commutator identities … hold in `Ḡ`". That does not follow.
  Each identity `W = W′` (for instance `v c v⁻¹ = e_14(f_02)`) is obtained by multiplying matrices and simplifying
  with the ring relations. When the relations hold only modulo `J`, what one gets is `W′⁻¹W ∈ GL_n(R,J) ∩ EL_n(R)`.
- Its class in `Ḡ` lies in `(EL_n(R) ∩ GL_n(R,J))/EL_n(R,J)`, a relative-`K_1`-type group that is not trivial in
  general. So the relations hold exactly in `EL_n(R/J) = EL_n(R)/(EL_n(R) ∩ GL_n(R,J))`, not in `Ḡ`.
- The compression criterion needs `z̄ ∈ D_(B̄)(L̄)`, `z̄` central and `z̄^m = 1` as exact relations in the group it is
  applied to. Applying it in `EL_n(R/J)` kills `z̄` only under homomorphisms that factor through `EL_n(R/J)`. A
  homomorphism `θ : Ḡ → H` into an MF group need not factor, since nothing puts the congruence kernel into `ker θ`.

**Candidate repairs** (not carried out here).
1. Induct with the congruence hypothesis `EL_n(R) ∩ GL_n(R,J) ≤ Rad_MF(EL_n(R))`. Then radical descent applies to
   `EL_n(R) → EL_n(R/J)` exactly, and the absolute proposition in `R/J` gives the step. The induction then needs the
   congruence form at the next stage, which is again a relative `K_1` question.
2. Run the construction in the Steinberg group `St_n(U_m)`, `U_m = Z⟨σ,τ⟩/(τσ − 1, m(1 − στ))`.
   - The assignment `x_ij(x) ↦ e_ij(lift(φ(x)))` is well defined into `Ḡ`: the Steinberg relations hold modulo `J`
     at generator level.
   - But the identities of the construction hold in `EL_n(U_m)`, so one needs control of `K_2(n, U_m)`.
3. Prove a relative commutator formula strong enough that the discrepancies above lie in `EL_n(R,J)`. This is not
   available for arbitrary noncommutative rings.

**Consequences.**
- (1c) inherits the gap at the successor step. Stage 0 and limits are fine.
- (1d): the right containment is correct as stated (a reduction to the MF group `EL_n(R/hh)`). The left containment is
  (1c).
- The model tests of artifact §6 (`hh = R` for simple non-directly-finite rings, `hh = 0` for the Pestov ring, the
  Toeplitz–Jacobson case) are unaffected: there `J = 0`, or the manuscript proves the equality directly.

## 3. un-open-8: PASS

**(2a) Lemma C.**
- `ψ(c)` commutes with `ψ(L)`, hence with `S`.
- `ψ(ucu⁻¹)` commutes with `ψ(u)Sψ(u)⁻¹ = S ∋ ψ(l)`.
- **Finite `H`:** `ψ(u)ψ(L)ψ(u)⁻¹ ⊆ ψ(L)` with equal cardinality.
- **`GL_d(K)`:** the Zariski closure `S` of `ψ(L)` is a closed subgroup whose centralizers are closed.
  `ψ(u)Sψ(u)⁻¹ ⊆ S` is a closed subgroup of the same dimension and the same number of components (components of an
  algebraic group are cosets of `S°`), so it equals `S`.
- `D_G(L)` matches tex eq. `intrinsic-defect` (l.167).

**(2b) The cell, re-derived** (tex `lem:ring-compression-cell`, l.866–929).
- **The factors.** In the `(i,4)` block,
  `e_4i(t−1)e_i4(1)e_4i(s−1)e_i4(−t) = [[1,0],[t−1,1]][[1,1],[0,1]][[1,0],[s−1,1]][[1,−t],[0,1]]`.
  Multiplying gives `[[1,1],[t−1,t]]`, then `[[s,1],[ts−1,t]] = [[s,1],[0,t]]`, then `[[s, 1−st],[0,t]] = [[s,e],[0,t]]`.
- **The compressor.** `u = u_3u_2u_1` has rows `(s,0,0,e)`, `(0,s,0,et)`, `(0,0,s,et²)` and `(0,0,0,t³)`.
- **Intertwining.** `u e_ij(a)` adds `sa` at `(i,j)`. `e_ij(sat)u` adds `sat·s = sa` at `(i,j)` and `sat·et^(j−1) = 0` at
  `(i,4)`.
- **The central element.** `c = [e_41(e), e_14(t)]`. In the `(1,4)` block this gives `[[1,0],[0,1+et]]`, using
  `te = 0`.
- **The key identity.** `uc` multiplies column 4 by `1+et`, giving `(e+et, et, et², t³)`, using `e² = e` and `te = 0`.
  `e_12(e)u` adds `e·(0,s,0,et) = (0,0,0,et)`, using `es = 0`. So `ucu⁻¹ = e_12(e)` and `[e_12(e), e_23(1)] = e_13(e)`.
- **The spread.**
  - `[e_13(e), e_32(b)] = e_12(eb)` and `[e_31(a), e_12(eb)] = e_32(aeb)`.
  - Signed permutations move this to every root, and additivity gives `E_N(R, ReR)`.
- **Simple case:** `ReR = R`.

## 4. Demotion state after review (checked at tip, 2026-09-13)

- **`relative-torsion-defect-mf-radical-step`: OPEN.** The owner withdrew the route at `27aa7b6a1`, and no route
  targets the claim.
  - Attempts carry the exact gap and both repair routes: congruence-kernel invisibility as the induction hypothesis,
    and the `St_n(U_m)` construction with `K_2(n,U_m)` control.
- **`mf-radical-contains-hilbert-hotel-elementary-subgroup`: OPEN / conditional.** Its only route requires the open
  step, so it does not fire. Attempts added: the gap, repairs A and B, and the unconditional case `hh = d`.
- **`mf-radical-sandwiched-by-hilbert-hotel-radical`: PASS after restatement.** The owner split cleanly.
  - The left bound is now the first-stage defect ideal, `EL_n(R, d) ≤ Rad_MF(EL_n(R))`, through
    `mf-radical-contains-defect-ideal-elementary-subgroup`, reviewed PASS below. The right containment is unchanged.
  - The `hh`-level bound lives in the open node above.
- **Reviewed PASS here:**
  - `mf-radical-contains-defect-ideal-elementary-subgroup`. Every defect of `R` itself is an exact one-sided pair with
    finite additive order, and the absolute printed proposition applies. Normal spreading plus additivity give
    `EL_n(R, d(R))`.
  - `congruence-invisible-ideal-torsion-defect-step`. Radical descent through the exact reduction kernel
    `EL_n(R) ∩ GL_n(R,J)`, the absolute statement over `R/J`, and pull-back. It uses no identity in a quotient group,
    so the gap does not arise.
- **Route audit:**
  - no `requires: []` route targets either open node;
  - `mf-radical-contains-hilbert-hotel-elementary-proof` requires the open step;
  - `mf-radical-sandwiched-by-hilbert-hotel-proof` requires only the established first-stage node.

## 5. Subsumption correction for (2a) and (2b)

My §3 PASS lines stand for correctness, but my subsumption scan missed three older nodes. Credit and `distinct_from`
entries are now on both nodes.

- **(2a) `compression-defects-die-in-rigid-targets` is subsumed as a theorem.**
  - `compression-defect-dies-in-finite-dimensions` (established and Lean-certified,
    `compressionCentralizerDefect_le_ker`) states that every homomorphism into `GL_k(V)` over every field, with
    `dim V < ∞`, kills the intrinsic defect.
    - Its defect is at least as large as this node's: compressors are generated as a group.
    - It contains the linear case directly.
    - It contains the finite case through the regular representation.
  - `locally-residually-finite-targets-kill-compression-defects` contains the finite case, by the same counting, for
    finitely generated `L`.
  - `zariski-envelope-compression-rigidity` is the Zariski rigidity over `C`.
  - Genuinely new: Lemma C, a target-agnostic support lemma, and the Zariski-closure proof over arbitrary fields.
- **(2b) `one-sided-defect-ideal-dies-in-linear-images-of-el`: new as a composition.** It combines the printed cell
  with the older finite-dimensional theorem. No older node states this for arbitrary unital rings.
  - Specific instances were recorded before, for the binary Jacobson ring.
  - `finitary-linear-extension-kazhdan-defect-kills-kernel` is a different statement: MF-level, through (T), over `F_2`.
