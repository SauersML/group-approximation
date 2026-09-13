# One ladder behind the non-MF paper and the Pestov 9.1 answer — synthesis, part 2 of 3

Lane `un-synthesis`, 2026-09-13, refresh 3 (main tip 6e4ef12930). Status tags and review landings as in part 1.

## 7. The paradox mechanism

### 7.1 The simple core: one compression lemma, read by the target

**Lemma C** [PASS for correctness · cf2fc07fe6; **SUBSUMED as theorems**, correction e4a5be7585;
`compression-defects-die-in-rigid-targets`]. Let `ψ : G → H`, `uLu⁻¹ ≤ L`, `c ∈ C_G(L)` and `l ∈ L`. Suppose some `S ≤ H`
satisfies:
- (S1) `S ⊇ ψ(L)`;
- (S2) everything commuting with `ψ(L)` commutes with `S`;
- (S3) `ψ(u)Sψ(u)⁻¹ = S`.

Then `ψ([ucu⁻¹,l]) = 1`.

| target | rigid support `S` | rigidity input | conclusion | (T) needed |
|---|---|---|---|---|
| finite group | `ψ(L)` | counting | `ψ(𝔇_G L) = 1` | no |
| `GL_d(K)` | Zariski closure | dimension, components | `ψ(𝔇_G L) = 1` | no |
| directly finite ring model | (ring level) | rank | `φ(ReR) = 0` | no |
| MF group (norm corona) | range of the Kazhdan projection in the adjoint corona | stable finiteness of the corona (tex l.478) | HS-invisible; exact on a normal (T) `K ≤ 𝔇` (l.646) | yes |
| tracial ultraproduct | none known | — | [OPEN] `hyperlinear-groups-kill-rigid-compression-defects` | — |

**Credit** (correction e4a5be7585). The finite and linear rows are older theorems:
- `compression-defect-dies-in-finite-dimensions`, established and Lean-certified as `compressionCentralizerDefect_le_ker`,
  which covers every field;
- `locally-residually-finite-targets-kill-compression-defects`;
- `zariski-envelope-compression-rigidity`, over ℂ.

What is new here is only the **target-agnostic support lemma** and the **Zariski-closure proof over arbitrary fields**.

**Linear images** [PASS · cf2fc07fe6, new as a composition; `one-sided-defect-ideal-dies-in-linear-images-of-el`]. For `ts = 1`
and `N ≥ 4`, every homomorphism from `EL_N(R)` to a finite or linear group kills `E_N(R,ReR)`, with no (T). It combines the
printed rank-four cell with the older finite-dimensional theorem.

**Reading.** The non-MF paper has a full defect, so rigid targets see nothing. Pestov's ring is directly finite, so no ring
defect exists and exact matricial models can exist.

### 7.2 Exact rank thresholds

- **Theorem P** [PASS · f15928d5c9; canonical `stably-infinite-ring-elementary-groups-have-no-mf-quotient`, with duplicates
  PASS]. If `2n[1] ≤ n[1]` in `V(R)`, every homomorphism from `EL_N(R)` to an MF group is trivial for `N ≥ 2n`. Novelty: NEW
  (bounded), a routine corollary of tex l.918.
- **Non-IBN** [PASS · d60f405998]. If `R^m ≅ R^(m+d)`, the same holds for `N ≥ max(m+1,3)`.
- **Groupoids without invariant measure** [PASS · f15928d5c9, `no-invariant-measure-steinberg-elementary-no-mf-quotient`].
  No MF quotient from rank `2n`, via Rainone–Sims Tarski and ABBL [imports, PASS].
- **Almost unperforated `S(𝒢)`** [PASS · fbaddd57b0, `unperforated-paradox-makes-steinberg-purely-infinite`]. An invariant
  measure exists, or the algebra is properly purely infinite with no MF quotient of any `EL_n`, `n ≥ 2`.

### 7.3 The MF spectrum of a ring

[PASS · 7c7fdace42, `mf-rigidity-is-monotone-in-matrix-rank`, `mf-thresholds-rescale-under-matrix-amplification`.]
- **Thresholds.** `mf(R) = sup{N : EL_N(R) MF}` and `rig(R) = min{N : EL_N(R) MF-rigid}`, with `mf < rig`.
- **Monotonicity.** MF is a down-set and rigidity an up-set in `N`, so the ranks split into MF, middle and rigid regimes.
- **Rescaling.** `rig(M_m R) = max(2, ⌈rig(R)/m⌉)`, and `mf` rescales by `⌊·/m⌋`.
- **Calibration.** Pestov's ring has `(mf, rig) = (∞, ∞)`; `L_k(1,2)` has `(1, 2)`.

**(M⇐), correct form** [Proposition R, un-m-converse 6afb261048, unreviewed; node wording PASS · e07954d78e].
- For countable simple `R`: `R` not stably finite ⟹ `rig(R) < ∞` [PASS].
- (M⇐) ⟺ every simple stably finite `R` has `mf(R) = ∞` ⟺ `rig(R) = ∞` **and** the middle regime is empty.
- So (M⇐) is a **rigidity half** plus a **lifting half**. The earlier synthesis wording ("empty middle regime", or "`mf = ∞`
  or `rig < ∞`") identified three different statements. It is withdrawn.

**Theorem S** [PASS · e07954d78e, folklore in substance; `simple-el-group-middle-regime-is-a-central-extension-effect`].
If every normal subgroup of `EL_N(R)` is central or everything:
- every nontrivial MF image of `EL_N(R)` has central kernel;
- with trivial centre, `EL_N(R)` is MF iff it has a nontrivial MF image;
- so a middle rank means MF fails to lift through a central extension.

**Corollary S2** [PASS · e07954d78e, with a scope repair: non-Hausdorff case only when the centre is `F_2`;
`f2-steinberg-elementary-groups-have-no-middle-mf-regime`]. Over `F_2` Steinberg algebras of minimal effective groupoids,
the middle regime lies in `{2}`. So there (M⇐) is exactly its rigidity half.

**The Toeplitz–Jacobson algebra** [theorem unreviewed; wording PASS · e07954d78e; `toeplitz-ring-has-infinite-middle-mf-regime`].
`J = F_2⟨s,t | ts=1⟩` has `mf ≤ 3` and `rig = ∞`, so every `N ≥ 4` is a middle rank. `J` is not simple (its defect is not
full), so simplicity is needed for S2.

**Which invariant rigidity measures.** For simple `R`, the rigid side is monoid-level: no nonzero state on `V(R)`, a Morita
invariant. The LEF side is not monoid-level (refutation F3).

### 7.4 The defect-ideal sandwich and a realised object

[un-review part8 · cf2fc07fe6.]
- **The radical** [PASS; `hilbert-hotel-radical-is-smallest-directly-finite-quotient`]. `hh(R)` is the smallest ideal with a
  directly finite quotient, built as a transfinite chain of defect ideals.
- **First stage** [PASS; `mf-radical-contains-defect-ideal-elementary-subgroup`]. If defects have finite additive order and
  `n ≥ 4`, then `EL_n(R, d(R)) ≤ Rad_MF(EL_n R)`, where `d(R)` is the ideal generated by all defects `1−st`, `ts = 1`.
- **The sandwich, restated with `d(R)`** [PASS; `mf-radical-sandwiched-by-hilbert-hotel-radical`]. If `EL_n(R/hh)` is MF, then
  `EL_n(R, d) ≤ Rad_MF(EL_n R) ≤ EL_n(R) ∩ GL_n(R, hh)`.
- **Also PASS:** `congruence-invisible-ideal-torsion-defect-step` and `zero-dimensional-wandering-clopen-sets-give-ring-defects`.
- **OPEN, after the review found a gap** (matrix identities hold only modulo the congruence kernel, not modulo `EL_n(R,J)`):
  - `relative-torsion-defect-mf-radical-step`, route withdrawn;
  - `mf-radical-contains-hilbert-hotel-elementary-subgroup`, conditional on that step;
  - `hilbert-hotel-radical-is-reached-in-one-step`.

**The predicted object is realised** [PASS · c341a29e49, n ≥ 4; `toeplitz-subshift-kazhdan-group-has-pestov-mf-quotient`,
lane un-hh-extension b9b25645e6]. Take `Y` an infinite minimal subshift. Let `R ⊆ End(⊕_i LC(Y,F_2) b_i)` be generated by
the shift-and-step isometry `s`, its one-sided inverse `t` and the letter indicators, and put `J = R(1−st)R`. Then:
1. `R` is finitely generated, `J ≅ M_∞(A_+)` is locally matricial, `R/J` is the Pestov ring, and `hh(R) = d(R) = J`;
2. `EL_n(R)` is finitely generated and Kazhdan for `n ≥ 3`;
3. for `n ≥ 4`, `Rad_MF(EL_n R) = EL_n(R,J)` is locally finite, nontrivial and proper, so `EL_n(R)` is not MF;
4. the maximal MF quotient `EL_n(LC(Y,F_2)⋊ℤ)` is an infinite f.g. simple Kazhdan LEF group.

Scope: rank-`n` for `n ≥ 4`; Pestov's rank-3 group is its `n = 3` case, where the radical is not computed.

**Firewall** [PASS · c341a29e49; `transient-crossed-products-have-nonsimple-mf-quotients`, via the standard Conley lemma
`chain-transitive-core-has-no-transient-points`]. Zero-dimensional crossed products with transient dynamics never give a
simple maximal MF quotient. The object must leave the crossed-product world, and the Toeplitz extension does.

### 7.5 The unit-group face

[PASS · 811353c0ef, and PASS · d166da76b2.]
- **Paradox extreme** (`purely-infinite-steinberg-gl-max-mf-quotient-is-k1`). Under local compressibility the maximal MF
  quotient of `GL_n(A_k 𝒢)` is `K_1`.
- **Irreducible SFT Leavitt algebras** (`irreducible-sft-leavitt-gl-max-mf-quotient-formula`). The quotient is
  `(Coker(1−Nᵗ)⊗k^×) ⊕ Ker(1−Nᵗ) = (H_0(G_A)⊗k^×) ⊕ H_1(G_A)`, via the Matui import [PASS verbatim]. The `K_1` formula is
  PRIOR (Ara–Brustenga–Cortiñas).
- **Exactly matricial extreme** (`steinberg-gl-mf-radical-is-commutator-or-trivial`). The radical is trivial there; the two
  extremes are exclusive, not exhaustive.
- **Full groups** [PASS · d166da76b2].
  - `lrf-cantor-actions-give-lef-full-and-elementary-groups`: one finite model makes both the full group and the Kazhdan
    `EL_n` LEF. The full-group half is PRIOR (Grigorchuk–Medynets, Ma).
  - `leavitt-mf-quotients-see-thompson-vd-through-parity`: MF quotients see Thompson's `V_d` only through parity, and `V`
    lies in the MF radical of binary Leavitt units.
- **[OPEN]** `steinberg-gl-max-mf-quotient-is-low-degree-homology` and
  `quantum-matricial-models-separate-full-groups-from-elementary`.

## 8. The measure mechanism

### 8.1 The Tarski chain

[PASS · 2ba472b59d; `algebraic-tarski-for-steinberg-algebras`, item 1 repaired to "faithful".] For minimal `𝒢` with compact
unit space, the chain is:
- a faithful Sylvester rank function ⟹ stably finite;
- stably finite ⟹ `θ` completely non-paradoxical;
- completely non-paradoxical ⟺ an invariant probability measure exists.

**Ring-level Tarski** [PASS · 638d4941b5; FOLKLORE].

### 8.2 Characteristic zero is exact, but property (T) lives only in characteristic p

- **Characteristic 0** [PASS · 2ba472b59d, f15928d5c9]. An invariant measure gives a faithful rank function through the
  finite von Neumann algebra of `∫ f|_X dμ`, so all four conditions of §8.1 are equivalent.
- **(T) only in characteristic p.** EJZ needs a finitely generated ring, and a field that is finitely generated as a ring is
  finite (Artin–Tate). So every Kazhdan example lives over a finite field.
- **Kaplansky firewall** (`measure-side-stable-finiteness-contains-char-p-kaplansky`). "Measure ⟹ stably finite" for free
  minimal Cantor actions over `k` would prove Kaplansky's stable finiteness conjecture over `k`. [OPEN]
  `invariant-measure-gives-rank-function-any-field`.
- **Consequence.** The Kazhdan groups live exactly where "measure ⟹ matricial" is not a theorem. The measure branch is
  witnessed by hand: Pestov's towers, Kerr–Nowak towers, Følner models.

### 8.3 Rank models without towers

- **Amenable acting groups** [PASS · 560decb046; `amenable-minimal-crossed-products-have-faithful-rank-models`]. Følner
  truncation gives a faithful rank model for `LC(X,k)⋊Γ` over any field. The older
  `free-minimal-crossed-products-are-simple-with-rank-models` already covers free actions.
- **Elek's algebraic amenability** [PASS, **PRIOR**: Arzhantseva–Păunescu Cor 11.15 · 5c8c71e333;
  `simple-amenable-affine-algebras-have-unital-rank-models`]. Simple amenable affine algebras have unital rank models.
- **Growth** [PASS · 5c8c71e333]: `subexponential-growth-simple-algebras-have-rank-models` and
  `zero-entropy-subshift-pestov-ring-has-rank-model-by-growth`.
- **Complexity** [PASS after a scope repair adding freeness; SUBSUMED in the free case · 5c8c71e333;
  `subexponential-complexity-zd-subshift-rings-have-rank-models`].
- **Labbé's shift** [PASS · 5c8c71e333; `labbe-wang-shift-has-polynomial-pattern-complexity`, with the import
  `labbe-substitution-is-primitive-and-recognizable`]. The shift is free, so the Labbé ring has a rank model.
- **[OPEN]** `positive-entropy-subshift-crossed-product-is-amenable`.

### 8.4 Which acting groups turn measures into towers

[PASS · 97bf4bc468 unless noted.]
- **Towers over every residually finite group, Kazhdan groups included** (`rf-toeplitz-subshifts-over-residually-finite-groups`,
  Theorem T). Every f.g. infinite residually finite `Γ` has a free minimal RF Toeplitz subshift with an invariant measure.
  So `EL_n` over it is LEF and Kazhdan (`residually-finite-group-toeplitz-elementary-groups-lef-kazhdan`, PASS, with a
  wording GAP: add a primitive element of `F_q`).
- **The class `𝔑`:**
  - closed under subgroups and finite-index overgroups;
  - contains every virtually free group (credit GAP: Kerr–Nowak Lemma 5.1);
  - excludes `ℤ²`.
  - [OPEN] `measure-rf-class-is-exactly-virtually-free-groups`.
- **Proposition S** (`rf-subshifts-are-periodic-window-approximable`): PASS, with a GAP on the paraphrase of Ma's statement.

### 8.5 The middle rung is realised: linear sofic, not LEF

[PASS · 560decb046; wiring PASS · 1df28bd83f; `simple-kazhdan-linear-sofic-non-lef-group-exists`.] Let `Γ_p` be the
Abels–Prüfer group, `X` a free minimal subflow and `R = LC(X,F_q)⋊Γ_p`. Then `S_N = EL_N(R)/Z` (`N ≥ 3`) is:
- infinite, finitely generated, simple and Kazhdan;
- `F_q`-linear sofic;
- not LEF, since `Γ_p ↪ S_N`.

So `R` has rank models but is not exactly matricial, and rungs (L) and (Σ) are distinct among simple rings with Kazhdan
groups. Soficity, hyperlinearity and MF of `S_N` are open.

## 9. Traces and operator algebras

- **MF traces** [PASS · 10083fd646, with credit and naming fixes]. The "corona traces" are Schafhauser's MF traces
  (arXiv:1705.06555), a PRIOR concept.
  - LEF ⟹ the canonical trace is MF ⟹ operator MF.
  - For an infinite LEF Kazhdan group with no finite quotients, the realising map has no ucp lift.
- **Separation** [PASS (ii)–(iv) · 10083fd646; (i) was conditional on Theorem P, which has since passed]. Only the trivial MF
  trace exists on the paradox branch, while the canonical trace is MF on the measure branch. This is a trace-level reading of
  tex l.918, not a new invariant.
- **Kazhdan collapse** [PASS; SUBSUMED by `stw10-kazhdan-full-group-traces-are-qd`; PRIOR Kirchberg 1994]. For Kazhdan groups,
  amenable ⟺ QD ⟺ a finite-dimensional limit. The ring criterion `τ_(EL_n R)` amenable ⟺ `R` residually finite is PASS; its
  ring step is FOLKLORE. So the canonical trace is blind to the dichotomy.
- **Reduced C*-algebras** [PASS · d166da76b2].
  - **Paradox side decided** (`measure-free-steinberg-el-n-reduced-cstar-not-mf`). For `N ≥ 2n`, every nontrivial quotient
    has a separable, stably finite, not MF reduced algebra.
  - **Measure-side firewalls:**
    - infinite simple groups are not PMF (`minimally-almost-periodic-groups-are-not-pmf`, folklore-level);
    - ring-induced models carry invariant vectors for non-amenable stabilisers, so they never converge strongly
      (`ring-model-permutation-vectors-block-strong-convergence`).
  - [OPEN] `free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure`. Its sufficiency half implies the famous root
    `infinite-kazhdan-group-with-mf-reduced-cstar`.

## 10. The coarse face

[PASS · 811353c0ef.]
- **RF-rigidity is free** (`un-ladder-rf-rigidity-is-free-mf-rigidity-is-dynamical`). At every rung the simple quotient has no
  nontrivial map to a residually finite or linear group. So the dichotomy lives entirely in the gap `RF ⊊ MF`.
- **A quasi-isometry invariant separates the ends** (`lef-infinite-simple-groups-are-qi-rigid`, with a scope note). A f.g.
  infinite simple LEF group is not finitely presented, so it is QI to no finitely presented group. This uses Vershik–Gordon,
  PRIOR.
  - Every measure rung is such a group, while the non-MF paper supplies finitely presented Kazhdan groups with no MF quotient.
- **[OPEN]** `paradox-side-elementary-group-is-finitely-presented` and `elementary-group-lef-growth-separates-subshifts`.
