# Formalization plan: *One-sided Kazhdan transport and MF radicals*

Spec document: `non_mf_groups_exist.tex` (title: **One-sided Kazhdan transport
and MF radicals**), 1056 lines, 3 lettered theorems + 12 numbered
environments + the displayed equations and prose claims they depend on.

> **Scope note.** `metadata/NON_MF_PROOF_LEDGER.md` audits a *different,
> historical* manuscript (the 2026-08-22 paper/notes split, 1486 lines). The
> present `.tex` has no ledger. This document is the plan to give it one.

## 0. Verdict

**66 checkable obligations.** Against the current development:

| | count | meaning |
| --- | --- | --- |
| **CARRIED** | 27 | an existing decl already proves it, at equal or greater strength |
| **ADAPT** | 18 | existing machinery + a restatement/bridge lemma |
| **NEW** | 19 | no supporting decl exists |
| **CITED** | 2 | genuine external theorem, no in-repo route |

The analytic half of the paper (Sections 1, 3, 4) is **almost entirely already
formalized** — the compression criterion, the shadow residual, the normal-Kazhdan
obstruction, corona stable finiteness and corner lifting all exist and are
audited. The algebraic half (Sections 5, 6, 7 — the rank-12 Leavitt
self-compression, simplicity, and the prescribed-quotient amalgam) is where
essentially all the new work is.

**The critical path to `Rad_MF(H) = H` needs no literature input at all**, and
in particular does **not** need simplicity of `H` — see §4.1. Simplicity is a
separate, advertised clause of Theorem B and is the one place where an external
theorem (Preusser) has no in-repo route.

**Property (T) is not a citation here.** The manuscript cites
Ershov--Jaikin-Zapirain, but `PropertyT/FiniteFieldElementaryPropertyT.lean:346`
already proves

```
finiteFieldElementaryThree_hasKazhdanPropertyT
  {k A : Type} [Field k] [Finite k] [Ring A] [Algebra k A] [Algebra.FiniteType k A] :
  HasKazhdanPropertyT.{0,0} (elementaryGroup (Fin 3) A)
```

unconditionally, and `LeavittFamily.rankSuccEquiv` transports it to every
positive rank. Both `L = EL₃(R)` and `H = EL₁₂(R)` are therefore covered with
zero external input.

## 1. Ground rules

Inherited from the existing manuscript lanes; deviating from any of these
breaks a gate.

1. **Thin-wrapper architecture.** New directory
   `GroupApproximation/Manuscript/OneSidedTransport/`. Every printed statement
   becomes a named `Prop` (binders *inside*, so `#audit_closed_axioms` accepts
   it) plus a `theorem manuscript<Name> : <Name>` whose proof is a reference
   into an implementation module. No mathematics in the wrapper layer.
   Pattern to copy verbatim: `Manuscript/MFRadicals/Definitions.lean`.
2. **Audit surface.** New `GroupApproximation/Endpoint/OneSidedTransportAudit.lean`
   printing every endpoint under `#audit_closed_axioms`. A green build *is* the
   proof of unconditionality; the macro rejects any leading caller-supplied
   binder and any axiom outside `propext / Classical.choice / Quot.sound`.
3. **Ledger + gate.** New `metadata/ONESIDED_TRANSPORT_LEDGER.md` (one row per
   printed statement) and `scripts/check_onesided_transport_ledger.py`, cloned
   from `scripts/check_mf_radical_ledger.py`. The three enforced failure modes
   stay the same: named decl must exist; must be printed in the audit; every
   `#audit_closed_axioms` line in the audit must appear in the ledger.
4. **Invariants that must not regress.** The development currently has
   **0 `sorry`** and **0 `axiom`** across 1965 files / 530k lines. Any clause
   that cannot be proved is recorded as a `conditional` ledger row carrying an
   explicit leading hypothesis — never as an axiom.
5. **Universes.** Analytic endpoints are proved at `Type 0` and lifted by the
   existing `Type0Transfer.exists_type0_model` / `CompressionUniverseTransfer`
   descent, exactly as `manuscriptIntrinsicNormalKazhdanRadical` does.
6. **Builds.** MSI only, short jobs, warm cache, `/projects/standard`. Never a
   full-library rebuild to check one module.

## 2. Claim inventory

IDs are stable handles for the ledger. `§` = manuscript section.

### 2.1 Introduction — definitions and the residual calculus

| ID | Statement | Status | Carrier / target |
| --- | --- | --- | --- |
| I-1 | `Q_d = ∏ M_{d_n}(ℂ) / ⊕ M_{d_n}(ℂ)`, `c₀`-direct sum | **CARRIED** | `Analysis/NormMatrixCorona.lean`: `NormMatrixCStarCorona`, `nullMatrixSequenceIdeal`, `norm_filterMatrixCorona_mk_eq_limsup` |
| I-2 | MF ⟺ finite-dim unitary models, defects → 0, asymptotic separation | **CARRIED** | `Sofic/CDEOperatorMF.IsCDEOperatorMF`; corona/unitary-sequence bridge `Analysis/NormMatrixCoronaUnitary.normMatrixCoronaUnitaryEquiv` |
| I-3 | `Rad_MF(G) = ⋂_d ⋂_π ker π` | **CARRIED** | `Sofic/ActualCoronaMFRadical.manuscriptCoronaMFResidual` (literal natural-dimension form) `= actualCoronaMFResidual` |
| I-4 | `G` MF ⟺ `Rad_MF(G) = 1` | **CARRIED** | `isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot` |
| I-5 | `Rad_MF(G)=G` ⟹ every hom to an MF group is trivial | **ADAPT** | one line from I-4 + `existsUnique_..._factorization_to_isCDEOperatorMF` |
| I-6 | `cl_MF^G(N) = ⋂{ker f : N ≤ ker f, f : G → M, M MF}` | **ADAPT** | `actualCoronaMFClosure` exists but is defined as `q_N⁻¹(Res_MF(G/N))`; needs the *literal* intersection-over-MF-targets form + an equality lemma |
| I-7 | corona image is countable and MF; every MF target embeds in a corona; hence `Rad_MF = cl_MF(1)` | **CARRIED** | `CoronaImageNormalKazhdan.nk_02_countable_mf_image`; `exists_actualCoronaRepresentation_ker_eq_actualCoronaMFResidual` |
| **P-1.1** | **MF residual calculus** (fully invariant; `G/Rad` MF; `G/N` MF ⟺ `cl(N)=N`) | **ADAPT** | 3 of 4 clauses carried (`map_actualCoronaMFResidual_le`, `actualCoronaMFQuotient_isCDEOperatorMF`, `Manuscript/MFRadicals/SemanticClosure.manuscriptSemanticClosure` clause 4). Full invariance under *endomorphisms* needs the one-line specialization of `map_..._le`. |
| P-1.1-pf | the diagonal-sum construction in the proof (enumerate, lift, take `n`-th partial direct sums, defects ≤ 1/n, half the separation survives because the quotient norm is a limsup) | **CARRIED** | this is exactly `CoronaImageNormalKazhdan.nk_03_separated_finite_models` + `norm_filterMatrixCorona_mk_eq_limsup` |
| I-8 | `Comp_G(L) = {u : uLu⁻¹ ≤ L}`; `𝔇_G(L)` (eq:intrinsic-defect); depends only on `(G,L)` | **ADAPT** | `compressionSet` is literally `Comp_G(L)`; but `compressionCentralizerDefectSet` conjugates by `g ∈ compressionGroup L` = the *subgroup generated*. See §4.2. |
| **A** | **one-sided compression criterion** | **CARRIED** | `Sofic/ManuscriptExactWrappers.manuscriptIntrinsicNormalKazhdanRadical` — literally `K ⊴ G`, `(T)`, `K ≤ compressionCentralizerDefect ι.range` ⟹ `K ≤ actualCoronaMFResidual G`. Strictly stronger than printed (§4.2). |
| A-i | nontrivial such `K` makes `G` non-MF | **ADAPT** | I-4 + A |
| A-ii | `G` Kazhdan and `𝔇_G(L)=G` ⟹ `Rad_MF(G)=G` | **ADAPT** | A with `K = ⊤` |
| A-iii | every fin-dim linear rep over every field kills `𝔇_G(L)` | **CARRIED** | `Criterion/CompressionCentralizerDefect.compressionCentralizerDefect_le_ker` |
| **B** | **the binary Leavitt group**: `H = EL₁₂(R)` nontrivial, simple, `(T)`, `Rad_MF(H)=H`, non-MF | **NEW** (assembly) | see W5–W7 |
| I-10 | eq:basic-defect (restatement of C-3.4) | **ADAPT** | wrapper over C-3.4 |
| I-11 | explicit data `τ, L, c=e₃₄(1), ℓ=e₁₂(1), d=e₀₂(q)` | **NEW** | W5 |
| I-12a | faithful fin-dim linear rep ⟹ `𝔇_G(L)=1` | **NEW** (short) | immediate from A-iii |
| I-12b | residually finite ⟹ `𝔇_G(L)=1` | **NEW** (short) | A-iii + RF ⟹ separated by finite quotients (`Sofic/SimpleNotLEF` style) |
| I-12c | amenable ⟹ `L` finite ⟹ `uLu⁻¹=L` ⟹ `𝔇_G(L)=1` | **CITED** | "amenable + (T) ⟹ finite" (BHV) — not in repo. Group-theoretic half (`L` finite ⟹ `uLu⁻¹=L` ⟹ defect trivial) is **NEW (short)** and worth doing regardless |
| I-13 | scope note: does **not** prove nonsofic / nonhyperlinear | **NEW (note)** | record as a prose row; optionally back it with the existing `Sofic/LiteralSoficSeparation` separation facts |
| **C** | **prescribed MF quotients** | **NEW** | W8 |

### 2.2 §2 — finite dimension

| ID | Statement | Status | Carrier / target |
| --- | --- | --- | --- |
| **T-2.1** | fin-dim commutant rigidity: `ρ(u)ρ(L)'ρ(u)⁻¹ = ρ(L)'` | **CARRIED** | `Criterion/CommutantRigidity.commutant_no_growth` / `commutant_no_growth'`, via `adjointRep` + `commutantStabilizer` |
| T-2.1-cor | `ρ([ucu⁻¹,ℓ]) = 1` | **CARRIED** | `map_compressionCentralizerDefect_generator_eq_one` |
| R-2.2 | the fin-dim hypothesis is essential (injective non-surjective endomorphism in infinite dimension) | **CARRIED** | `Sofic/KazhdanTransportFiniteDimensionalInputs`: `shiftDown_mul_shiftUp`, `shiftUp_mul_shiftDown_ne_one`, `not_dedekindFinite_infiniteDimensionalModel`, `isDedekindFinite_finiteDimensionalModel`, `finiteDimensionality_used_twice` |

### 2.3 §3 — Kazhdan transport

| ID | Statement | Status | Carrier / target |
| --- | --- | --- | --- |
| D-3.1 | `‖a‖₂ = tr_d(a*a)^{1/2}`, `tr_d = Tr/d` | **CARRIED** | `Sofic/HyperlinearScalar.hsNormSq`, `Sofic/LeavittTraceFloor.hsNorm` |
| D-3.2 | operator-norm asymptotic representation | **CARRIED** | `Sofic/OpAlmostRepresentation.OpAlmostRepresentation` (`V_n(1)=1` is the only cosmetic difference; harmless) |
| D-3.3 | `K₂(V)`, and it is normal | **ADAPT** | kernel of `(toAsymptoticUnitaryRepresentation B).toUltraproductHom`; needs a *named* `K₂` with **ordinary** convergence + the bridge "→0 ordinarily ⟺ →0 along every ultrafilter ≤ cofinite" |
| D-3.4 | `R_{∞→2}(G) = ⋂_V K₂(V)` (eq:shadow-residual), normal | **CARRIED** | `Sofic/OpToHSShadowResidual.opToHSShadowResidual` (+ `opToHSShadowResidual_isFullyInvariant`, stronger than printed) |
| **L-3.1** | norm matrix corona is stably finite; equivalent projections `p ≤ q` ⟹ `p = q` | **CARRIED / ADAPT** | first half: `Analysis/MatrixCoronaDedekindFinite.mul_eq_one_symm_matrixCorona` + `cstarMatrix_mul_star_eq_one_of_hasMFEmbedding` + `mfAlgebra_isStablyFinite`. Second half (**projection order from stable finiteness**, via `w + (1-q)` isometry) is **NEW (short)**. |
| **L-3.2** | one-sided order for the Kazhdan projection: `Uπ(L)U* ⊆ π(L)` ⟹ `U*PU ≤ P` | **NEW** | needs `p_L ∈ C*_max(L)`, its image in a unital `C*`-algebra `B`, and `range = Fix π(L)` in a faithful nondegenerate representation. See §4.3. |
| **T-3.3** | **one-sided Kazhdan transport** | **ADAPT (printed route NEW)** | conclusion is reachable from the existing ultraproduct route; the *printed* route (the six sub-steps below) is new |
| T-3.3-a | `‖Ad A − Ad B‖ ≤ 2‖A − B‖` for unitaries | **NEW (short)** | |
| T-3.3-b | conjugation on `M_{d_n}(ℂ)` with normalized HS inner product; Hilbert ultraproduct `K_ω`; `σ` is a unitary rep of `G` | **CARRIED** | `Analysis/VectorHilbertUltraproduct` (`HOmega`, `uvinner`), `Analysis/VectorOmegaAction` |
| T-3.3-c | `B = ∏ B(M_{d_n}(ℂ))/⊕` *is* a norm matrix corona with sizes `d_n²` | **ADAPT** | `Analysis/MatrixReindexHilbertSchmidt` + `Analysis/NaturalMatrixCoordinateEquiv` |
| T-3.3-d | `g ↦ σ̃(g)` is an exact homomorphism `G → U(B)` | **ADAPT** | from T-3.3-a + `NormMatrixCoronaUnitary` |
| T-3.3-e | `C*_max(L) → B`; `P` = image of the Kazhdan projection; range = `Fix σ(L)` | **NEW** | §4.3 |
| T-3.3-f | `U*PU ≤ P` (L-3.2) + unitary equivalence + L-3.1 ⟹ `U*PU = P`; ultrafilter-free conclusion | **NEW (assembly)** | |
| **C-3.4** | `[ucu⁻¹,ℓ] ∈ R_{∞→2}(G)` | **ADAPT** | `Sofic/OpToHSShadowResidual.witness_commutator_mem_opToHSShadowResidual` is the *witness-specific* instance; the general `Comp × C_G(L) × L` form is new but is a direct consequence of T-3.3 |

### 2.4 §4 — the canonical Kazhdan sector

| ID | Statement | Status | Carrier / target |
| --- | --- | --- | --- |
| **L-4.1** | central corona corners (projection lifting by spectral rounding, unitary lifting by polar correction, corner asymptotic rep) | **CARRIED** | `Analysis/CoronaProjectionLifting` (dimension-free spectral rounding), `Analysis/PolarLiftingMatrixBlocks`, `Analysis/PolarLiftingGeneralCStar`, `Analysis/PrintedCornerAssembly.exists_printedCornerData` |
| **T-4.2** | **normal Kazhdan radical theorem** (`D ≤ R_{∞→2}(G)`, `K ⊴ G` Kazhdan, `K ≤ D` ⟹ `K ≤ Rad_MF(G)`) | **CARRIED** | `Sofic/OpToHSShadowResidual.normalKazhdan_le_normMFResidual_of_le_opToHSShadowResidual`; printed route already reproduced by `Sofic/CoronaImageNormalKazhdan` (`nk_01`…`nk_05`, `manuscriptNormalKazhdanObstructionViaCoronaImage`) |
| T-4.2-a | `Θ(g)pΘ(g)* = p` from normality | **CARRIED** | inside `nk_04_moving_corner` |
| T-4.2-b | corner Kazhdan inequality `b ≥ (κ²/|S|)q` and the trace consequence | **CARRIED** | `InternalRadicalGap` corner machinery driven by `nk_03` |
| **Pf-A** | proof of Theorem A (assembly: C-3.4 + normality ⟹ `𝔇 ≤ R_{∞→2}`, then T-4.2) | **ADAPT** | one wrapper |
| **P-4.3** | functoriality and saturation | **ADAPT/NEW** | `f(𝔇) ≤ 𝔇_{f(G)}(f(L))`: **ADAPT** from `CompressionUniverseTransfer.compressionCentralizerDefect_map_le` (currently only for `MulEquiv`; needs arbitrary `f`). Simple-subgroup absorption + normal-closure saturation + the surjective-image clause: **NEW (short, pure group theory)**. |

### 2.5 §5 — the binary Leavitt self-compression (all NEW)

| ID | Statement | Status | Notes |
| --- | --- | --- | --- |
| D-5.1 | `R = L_{𝔽₂}(1,2)`, `p = s₀t₀`, `q = s₁t₁` | **CARRIED** | `Leavitt/UniversalLeavittOver.BinaryLeavittAlgebra (ZMod 2)`, `LeavittFamily` |
| E-5.2 | eq:pq — `p + q = 1`, `t₁ q s₁ = 1`, hence `q ≠ 0` | **ADAPT** | the two relations are `LeavittFamily` fields; `q ≠ 0` follows from `t₁qs₁=1` and `1 ≠ 0` |
| D-5.3 | corner embedding `GL₃(R) ↪ GL₁₂(R)`, `A ↦ diag(A, I₉)` | **NEW** | generalize the existing `coreEmbedding` (rank 3 → rank 4) to rank 3 → rank 12 |
| **E-5.4** | `Ψ(A) = qI₃ + s₀At₀` is unital, multiplicative, injective (`t₀Ψ(A)s₀ = A`) | **NEW** | pure ring calculation from `qs₀ = t₀q = 0`, `t₀s₀ = 1` |
| D-5.5 | `X`, `Y` as displayed; `XY = YX = I₆` | **NEW** | `2×2` block matrices over `M₃(R)`; direct calculation |
| D-5.6 | `τ = diag(X, Y) ∈ GL₁₂(R)` | **NEW** | |
| **E-5.7** | eq:whitehead-factorization — `diag(X, X⁻¹)` as the 6-factor product of block unipotents | **NEW** | the printed identity, verified as a `Matrix` equation |
| E-5.8 | each block unipotent is a product of elementary `12×12` matrices (entries inserted one at a time; matrix units have pairwise zero products) | **NEW** | the fiddliest single item in §5 — plan a reusable `blockUnipotent_mem_elementaryGroup` lemma over an arbitrary ring, indexed by a rectangular index-set split |
| **E-5.9** | `τ ∈ EL₁₂(R)` | **NEW** | E-5.7 + E-5.8 |
| **E-5.10** | eq:corner-conjugation — `τ diag(A,I₉) τ⁻¹ = diag(Ψ(A), I₉)` | **NEW** | block multiplication |
| E-5.11 | `Ψ(e_ij(a)) = e_ij(s₀at₀)` | **NEW** | |
| **E-5.12** | eq:compresses-L — `τLτ⁻¹ ≤ L`, i.e. `τ ∈ compressionSet L` | **NEW** | E-5.10 + E-5.11 |
| T-5.13 | `H` and `L` have property `(T)` | **CARRIED** | `finiteFieldElementaryThree_hasKazhdanPropertyT` + `LeavittFamily.rankSuccEquiv` + `HasKazhdanPropertyT.of_mulEquiv`; `L` via the corner embedding being injective |
| R-5.14 | remark on `𝔽₂` (trivial unit group) and on `12` carrying no minimality claim | **prose** | ledger row only |

### 2.6 §6 — the full MF radical

| ID | Statement | Status | Notes |
| --- | --- | --- | --- |
| **P-6.1** | `H = EL₁₂(R)` is **simple** | **CITED** | needs Preusser's normal-subgroup theorem. §4.1. |
| P-6.1-a | `R` purely infinite simple (Abrams--Aranda), exchange ring (Ara) | **CITED** | |
| P-6.1-b | `Z(R) = 𝔽₂` (Aranda--Crow) — and the self-contained argument the manuscript gives for `Z(GL₁₂(R)) = 1` | **NEW** | the manuscript's own argument (commute `z` with `e_ij(1)` to force `z = λI`, then with `e_ij(a)` to force `λ ∈ Z(R)ˣ`) is elementary and **should be formalized directly**, taking `Z(R)ˣ = {1}` as the cited input or proving it from the Leavitt normal form (`Leavitt/LeavittNormalForm.lean`) |
| P-6.1-c | `H ≠ 1` (`e₀₁(1) ≠ 1`) | **NEW (short)** | |
| **P-6.2** | `c = e₃₄(1) ∈ C_H(L)`; eq:moved-mark `τcτ⁻¹ = e₀₁(q)e₃₄(1)`; `d = e₀₂(q) ≠ 1`; `⟨⟨d⟩⟩_H = H` | **NEW** | last clause: **do not route through simplicity** — see §4.1 |
| **Pf-B** | proof of Theorem B | **NEW (assembly)** | |

### 2.7 §7 — prescribed MF quotients (all NEW)

| ID | Statement | Status | Notes |
| --- | --- | --- | --- |
| D-7.1 | `W_Q = B *_A (Q × A)`, `A = ⟨d⟩` | **ADAPT** | `Monoid.PushoutI` (mathlib, already used in `Sofic/TerminalQuotientPresentation.lean`) or `Higman/AmalgamPresentation.Amalg` |
| D-7.2 | `π_Q : W_Q ↠ Q` well defined, split by `Q → Q × A → W_Q` | **NEW (short)** | universal property of the pushout |
| D-7.3 | both vertex maps injective (normal form for amalgams); `d ≠ 1` in `W_Q` | **ADAPT** | mathlib `Monoid.PushoutI.of_injective` / normal-form API |
| **P-7.1** | universal factorization: `Hom(Q,T) ≅ Hom(W_Q,T)` for `T` killing `B`; `ker π_Q = ⟨⟨d⟩⟩_{W_Q}` | **NEW** | pure group theory once D-7.1–D-7.3 land |
| **Pf-C** | proof of Theorem C: `Rad_MF(W_Q) = π_Q⁻¹(Rad_MF(Q))`; `W_Q` non-MF; `Q` MF ⟹ `Rad = ker π_Q = ⟨⟨d⟩⟩` | **NEW (assembly)** | P-7.1 + I-5 + I-4 |
| E-7.2 | eq:closure-pullback `cl_MF^{W_Q}(N) = π_Q⁻¹(cl_MF^Q(π_Q N))` | **NEW** | |
| E-7.3 | `W_Q/N` MF ⟺ `ker π_Q ≤ N` and `Q/π_Q(N)` MF | **NEW** | E-7.2 + P-1.1 |

## 3. Work packages

Dependency order. Each package is one landing (green build + push), sized to a
short MSI job.

**W0 — scaffold (½ day).** Create
`Manuscript/OneSidedTransport/{Definitions,Criterion,Transport,Sector,Leavitt,Amalgam,MainTheorems}.lean`,
`Endpoint/OneSidedTransportAudit.lean`, `metadata/ONESIDED_TRANSPORT_LEDGER.md`,
`scripts/check_onesided_transport_ledger.py`. Wire the audit file into
`GroupApproximation.lean`. Land with the three already-CARRIED endpoints (A,
T-2.1, T-4.2) so the gate is live from day one.

**W1 — printed-defect bridge (1 day).** Define `manuscriptCompressionDefect L`
using the literal `compressionSet` (not `compressionGroup`); prove
`manuscriptCompressionDefect L ≤ compressionCentralizerDefect L`; restate
Theorem A, A-iii, C-3.4 and P-4.3 on the printed object. **This is the
single highest-value package**: it converts ~8 existing decls into
printed-fidelity rows at near-zero cost. (§4.2)

**W2 — residual calculus (1–2 days).** I-5, I-6, P-1.1. The literal
`cl_MF^G(N)` as an intersection over MF targets, and its equality with the
existing `actualCoronaMFClosure`. Full invariance under endomorphisms.

**W3 — the printed transport route (5–8 days, highest analytic risk).**
L-3.1 (projection order half), L-3.2, T-3.3-a…f, and the named `K₂` with
ordinary convergence (D-3.3). Gated on §4.3. **The conclusions are already
available by the existing route**, so W3 is *fidelity*, not reach: schedule it
after W5–W7 if the priority is the headline rather than the printed proof.

**W4 — sterility corollaries (1 day).** I-12a, I-12b, the group-theoretic half
of I-12c, R-2.2 (wrappers only), P-4.3 simple-subgroup clauses, I-13 note.

**W5 — Leavitt rank-12 compression (5–8 days).** D-5.3 through E-5.12,
T-5.13. Recommended internal order:
1. `blockUnipotent_mem_elementaryGroup` over an arbitrary ring for an arbitrary
   index split (E-5.8) — reusable, and the only genuinely fiddly lemma;
2. `X`, `Y`, `XY = YX = I₆` (D-5.5);
3. Whitehead factorization (E-5.7) as a literal `Matrix` identity;
4. `τ ∈ EL₁₂(R)` (E-5.9);
5. `Ψ` and its three properties (E-5.4);
6. corner conjugation and `τ ∈ compressionSet L` (E-5.10, E-5.12).
   Reuse pattern: `Leavitt/RankFourCompressors.lean` does the rank-4 analogue
   end to end (`compressorPiece`, `compressor_conjugation`,
   `coreEmbedding_compressorSet_generate`).

**W6 — normal generation, not simplicity (2–3 days).** P-6.2, including
`⟨⟨e₀₂(q)⟩⟩_H = H` **proved directly** (§4.1). Delivers `𝔇_H(L) = ⊤` without
any literature input.

**W7 — Theorem B (1 day + the simplicity decision).**
`Rad_MF(EL₁₂(L_{𝔽₂}(1,2))) = ⊤`, `H` non-MF, "not every countable group is
MF". Countability of `H` from `Leavitt/FiniteTypeCountable.lean`. The
`IsSimpleGroup H` clause is landed separately as a `conditional` row or as
P-6.1 if W9 runs.

**W8 — prescribed MF quotients (3–4 days).** D-7.1 through E-7.3. Independent
of W3/W5 — can run in parallel with them.

**W9 — simplicity (optional, 2–4 weeks).** P-6.1 in full: a normal-subgroup
theorem for `EL_n` over a simple exchange ring, plus `Z(R) = 𝔽₂` from the
Leavitt normal form. Only run this if the printed "simple" clause must be
machine-checked rather than cited. (§4.1)

## 4. The three real risks

### 4.1 Simplicity of `EL₁₂(R)` — and why the headline does not need it

The manuscript uses simplicity **twice**: to conclude `⟨⟨d⟩⟩_H = H`, and (via
Prop. 4.3) to conclude `H ≤ 𝔇_H(L)`. Both uses collapse to the single fact

> `d = e₀₂(q)` normally generates `EL₁₂(R)`.

and **that** is provable with elementary-matrix identities alone, from a
relation the manuscript already displays:

* eq:pq gives `t₁ q s₁ = 1`, so `1 ∈ R q R` outright — **no simplicity of `R`
  is needed**, and no purely-infinite/exchange-ring input either;
* `⁅e_{k0}(a), e₀₂(q)⁆ = e_{k2}(aq)` and `⁅e₀₂(q), e_{2m}(b)⁆ = e_{0m}(qb)`
  put `e_{km}(a q b)` in the normal closure for distinct `k,m`;
* taking `a = t₁, b = s₁` gives `e_{km}(1)`, and
  `⁅e_{kl}(a), e_{lm}(1)⁆ = e_{km}(a)` (needs `n ≥ 3`, and `12 ≥ 3`) gives every
  `e_{km}(a)`.

`Leavitt/ElementaryNoFiniteQuotients.elGen_commutator` already provides the
commutator identity. **Recommendation: prove W6 this way, land the headline,
and treat P-6.1 as a separately advertised clause.** Since `𝔇_H(L)` is normal
and contains `d`, `𝔇_H(L) ⊇ ⟨⟨d⟩⟩ = H` — Prop. 4.3's simple-subgroup clause is
never invoked on the critical path.

For P-6.1 itself there is no in-repo route: grep returns **no** Preusser, no
congruence subgroup `C_n(R,I)`, no relative elementary subgroup, and no
`IsSimpleGroup` for any elementary group. The center half (`Z(GL₁₂(R)) = 1`) is
elementary and the manuscript writes the argument out; the sandwich
classification is the whole cost.

### 4.2 The defect discrepancy (printed vs. formalized)

Printed: `u ∈ Comp_G(L)`, a **set** (a monoid, not a group).
Lean: `g ∈ compressionGroup L = closure (compressionSet L)`.

Consequence: `𝔇^printed ≤ 𝔇^Lean`, so the existing theorem
`manuscriptIntrinsicNormalKazhdanRadical` (hypothesis `K ≤ 𝔇^Lean`) **implies**
the printed Theorem A (hypothesis `K ≤ 𝔇^printed`). The direction is
favourable and W1 is a containment lemma, not a reproof. Do **not** be tempted
to weaken the Lean object to match: keep both, prove the containment, and state
every printed row on `𝔇^printed`.

Note also A-iii is likewise printed-weaker: `compressionCentralizerDefect_le_ker`
kills the larger group.

### 4.3 The `C*_max` Kazhdan projection (the one genuine analytic gap)

L-3.2 and T-3.3-e need, in this order:

1. `C*_max(L)` as a unital `C*`-algebra with its universal property for unitary
   representations. **Partially present**: `Analysis/CStarSeminormCompletion`,
   `Analysis/MaximalCStarAllUniverses`,
   `Analysis/MaximalGroupCStarUniqueness.starAlgEquiv_of_universalProperty`.
   **Verify before committing to W3.**
2. The Kazhdan projection `p_L ∈ C*_max(L)` for `L` with `(T)`, and the fact
   that its image in any unital `C*`-algebra `B` under `π : C*_max(L) → B`
   projects onto `Fix π(L)` in a faithful nondegenerate representation.
   `Analysis/OmegaCoronaKazhdanProjection.manuscriptKazhdanProjection` builds
   the projection **in the corona directly** (not in `C*_max`), and
   `Kazhdan/KazhdanProjection.norm_averageOperator_pow_sub_projection_le` gives
   the uniform orbit-average estimate that makes the limit converge in the
   `C*_max` norm. This is the bridge to build.

Mitigation if step 1 turns out to be more than it looks: state L-3.2 for a
`C*`-algebra `B` equipped with a *given* `π`-invariant projection satisfying
the Kazhdan inequality (which is what the corona proof actually consumes), and
mark the `C*_max` phrasing as a presentation-only row. Flag this as a
**decision point at the start of W3**, not a surprise mid-package.

## 5. Sequencing recommendation

If the goal is *the headline machine-checked as fast as possible*:

```
W0 → W1 → W5 → W6 → W7        (≈ 3 weeks; zero literature input)
```

with W2, W4, W8 landing in parallel gaps and W3, W9 afterwards. This yields
`Rad_MF(EL₁₂(L_{𝔽₂}(1,2))) = ⊤` and non-MF-ness under `#audit_closed_axioms`
with an empty telescope, i.e. unconditionally, while the printed proof route
of §3 and the `simple` clause remain open rows in the ledger.

If the goal is *every printed sentence has a row*, add W3 and W9 and expect
6–10 weeks.

## 6. Landing discipline

* One package per commit; every commit green under the audit gate.
* `scripts/prepush_source_scan.sh` before every push (lexical `sorry` scan).
* Never `git reset / amend / revert / stash / worktree / branch` — recover
  forward.
* Re-pin the ledger's manuscript hash whenever `non_mf_groups_exist.tex`
  changes, after reviewing the rows the edit touches.
