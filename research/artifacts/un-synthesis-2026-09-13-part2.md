# One ladder behind the non-MF paper and the Pestov 9.1 answer — synthesis, part 2 of 3

Lane `un-synthesis`, 2026-09-13, refresh 2 (main tip 938ae27b49). Status tags and review landings as in part 1.

## 7. The paradox mechanism

### 7.1 The simple core: one compression lemma, read by the target

**Lemma C** [unreviewed; un-open-8 3e2e7a2505, `compression-defects-die-in-rigid-targets`]. Let `ψ : G → H`, `L ≤ G`,
`uLu⁻¹ ≤ L`, `c ∈ C_G(L)` and `l ∈ L`. Suppose `S ≤ H` satisfies:
- (S1) `ψ(L) ⊆ S`;
- (S2) everything commuting with `ψ(L)` commutes with `S`;
- (S3) `ψ(u)Sψ(u)⁻¹ = S`.

Then `ψ([ucu⁻¹,l]) = 1`. So `ψ` kills the intrinsic defect `𝔇_G(L)` as soon as every compressor admits a *rigid
support*.

| target | rigid support `S` | rigidity input | conclusion | (T) needed |
|---|---|---|---|---|
| finite group | `ψ(L)` | counting | `ψ(𝔇_G L) = 1` | no |
| `GL_d(K)` | Zariski closure | dimension, components | `ψ(𝔇_G L) = 1` | no |
| directly finite ring model | (ring level) | rank | `φ(ReR) = 0` | no |
| MF group (norm corona) | range of the Kazhdan projection in the adjoint corona | stable finiteness of the corona (tex Thm l.478) | Hilbert–Schmidt invisible; exact on a normal (T) `K ≤ 𝔇` (Thm l.646) | yes |
| tracial ultraproduct | none known | — | [OPEN] `hyperlinear-groups-kill-rigid-compression-defects` | — |

**Readings.**
- The two papers are two readings of Lemma C:
  - **non-MF paper:** a full defect exists, so rigid targets see nothing;
  - **Pestov 9.1:** the ring is directly finite, so no ring defect exists and exact matricial models can exist.
- **Linear images** [unreviewed, `one-sided-defect-ideal-dies-in-linear-images-of-el`]. For `ts = 1`, `e = 1−st` and
  `N ≥ 4`, every homomorphism from `EL_N(R)` to a finite group or to `GL_d(K)` is trivial on `E_N(R,ReR)`, with no (T)
  and no finite generation. Property (T) is needed only at the MF level.
- **Model test:** in `GL_2(ℚ)` with `L` the integer unitriangulars and `u = diag(2,1)`, the defect is trivial, as it must
  be for a linear group.

### 7.2 Exact rank thresholds

- **Theorem P** [PASS · f15928d5c9; canonical `stably-infinite-ring-elementary-groups-have-no-mf-quotient`; same theorem
  PASS · d60f405998 `paradoxical-ring-el-n-full-mf-radical-from-twice-level`, PASS · 2ba472b59d
  `full-defect-in-m-by-m-kills-mf-quotients-of-el-2m`]. If `2n[1] ≤ n[1]` in `V(R)`, every homomorphism from `EL_N(R)`
  to an MF group is trivial for `N ≥ 2n`.
  - Proof: tex l.918 at rank 2 over `M_n(R)`, plus `EL_2(M_n R) = EL_(2n)(R)`.
  - Novelty: NEW (bounded), a routine corollary of the manuscript.
- **Non-IBN** [PASS · d60f405998 after a scope repair; `non-ibn-ring-el-n-full-mf-radical-above-module-rank`]. If
  `R^m ≅ R^(m+d)`, the same holds for `N ≥ max(m+1,3)`.
- **Groupoids without an invariant measure** [PASS · f15928d5c9, canonical `no-invariant-measure-steinberg-elementary-no-mf-quotient`;
  same theorem PASS · d60f405998 `measure-free-ample-groupoid-el-n-full-mf-radical`]. There is no MF quotient from rank
  `2n`. The chain behind it is Rainone–Sims Tarski [import, PASS], ABBL states→measures [import, PASS] and the bridge `ι`.
- **Almost unperforated `S(𝒢)`** [PASS · fbaddd57b0 after repair; `unperforated-paradox-makes-steinberg-purely-infinite`].
  Exactly one of these holds:
  - an invariant measure exists;
  - `A_k(𝒢)` is properly purely infinite and simple, and `EL_n` has no MF quotient for every `n ≥ 2`.

  The owner repair: exclusivity in characteristic `p`, and rank-two requires.

### 7.3 The MF spectrum of a ring

[PASS · 7c7fdace42: `mf-rigidity-is-monotone-in-matrix-rank`, `mf-thresholds-rescale-under-matrix-amplification`; novelty:
monotonicity FOLKLORE, rescaling NEW (bounded) routine.]

- **The two thresholds.**
  - `mf(R) = sup{N ≥ 2 : EL_N(R) MF}`.
  - `rig(R) = min{N ≥ 2 : every homomorphism from EL_N(R) to an MF group is trivial}`.
- **Monotonicity.** MF is a down-set in `N` and rigidity an up-set, with `mf(R) < rig(R)`. So the ranks split into three
  consecutive regimes: MF, the *middle* (not MF but with a nontrivial MF quotient), and rigid.
- **Rescaling.**
  - `rig(M_m R) = max(2, ⌈rig(R)/m⌉)`, and `mf(M_m R) = ⌊mf(R)/m⌋` (or 1).
  - The dichotomy conditions are stable under amplification; the threshold values are finer data.
- **Calibration.** Pestov's ring has `(mf, rig) = (∞, ∞)`; `L_k(1,2)` has `(1, 2)`.
- **Which invariant rigidity measures** [unreviewed reading]. For simple `R`: `V(R)` has no nonzero state ⟺ `R` not stably
  finite ⟹ `rig(R) < ∞`. This is a Morita-invariant, monoid-level condition. The LEF side is not monoid-level (refutation F3).
- **The middle regime is inhabited** [unreviewed; `toeplitz-ring-has-infinite-middle-mf-regime`; NEW (bounded) routine].
  The Toeplitz–Jacobson algebra `J = F_2⟨s,t | ts=1⟩` has `mf(J) ≤ 3` and `rig(J) = ∞`.
  - `J` is not simple, since its defect ideal is not full.
  - Hence (M⇐) reformulates exactly as: **for simple rings the middle regime is empty.**

### 7.4 The Hilbert-hotel radical sandwich

[unreviewed; un-open-1 36226184dd.]
- **The radical** (`hilbert-hotel-radical-is-smallest-directly-finite-quotient`). Iterate "ideal generated by the defects
  `1−st`, `ts = 1`" transfinitely. The result `hh(R)` is the smallest ideal with directly finite quotient.
- **The sandwich** (`mf-radical-sandwiched-by-hilbert-hotel-radical`). Let `R` have torsion additive group (e.g. an
  algebra in characteristic `p`) and `n ≥ 4`. Then:
  - `EL_n(R, hh(R)) ≤ Rad_MF(EL_n R)` (`mf-radical-contains-hilbert-hotel-elementary-subgroup`, from tex
    `prop:torsion-defect-ring` and the relative step `relative-torsion-defect-mf-radical-step`);
  - if `EL_n(R/hh)` is MF, then `Rad_MF(EL_n R) ≤ EL_n(R) ∩ GL_n(R, hh)`.
- **Reading.**
  - The paradox side supplies the radical, and the measure side supplies the hypothesis that `EL_n(R/hh)` is MF.
  - Model tests: `L_k(1,m)` (radical everything), Pestov (radical trivial), Toeplitz `J` (radical `EL_n(J, JeJ)`,
    agreeing with the printed computation).
- **Open.**
  - `hilbert-hotel-radical-is-reached-in-one-step`.
  - `zero-dimensional-hilbert-hotel-radical-is-core-ideal`, which would make the printed core theorem a corollary.
  - Predicted object: a Kazhdan group whose MF radical is proper and nontrivial and whose maximal MF quotient is an
    infinite simple LEF Kazhdan group.

### 7.5 The unit-group face

[unreviewed; un-k1-homology 5c83d35b84, un-full-groups-bridge 21ed3e7571.]
- **The paradox extreme** (`purely-infinite-steinberg-gl-max-mf-quotient-is-k1`). Under local compressibility the maximal
  MF quotient of `GL_n(A_k 𝒢)` is `K_1`.
  - For irreducible SFT Leavitt algebras (`irreducible-sft-leavitt-gl-max-mf-quotient-formula`) it is
    `(Coker(1−Nᵗ) ⊗ k^×) ⊕ Ker(1−Nᵗ)`, read as `(H_0(G_A) ⊗ k^×) ⊕ H_1(G_A)` through Matui.
  - The `K_1` formula is PRIOR (Ara–Brustenga–Cortiñas 0903.0056); the MF half is tex l.1218.
- **The measure extreme.** For exactly matricial algebras the radical is trivial (`steinberg-gl-mf-radical-is-commutator-or-trivial`).
  The two extremes are exclusive, not exhaustive.
- **Thompson's `V_d` inside Leavitt units** (`leavitt-mf-quotients-see-thompson-vd-through-parity`). MF quotients see
  `V_d` only through a parity character.
  - `V = V_2` lies in the MF radical over every field.
  - This says nothing about whether `V_d` itself is MF.
- **Open:** `steinberg-gl-max-mf-quotient-is-low-degree-homology`.

## 8. The measure mechanism

### 8.1 The Tarski chain

[PASS · 2ba472b59d; `algebraic-tarski-for-steinberg-algebras`, item 1 scope-repaired "nonzero" → "faithful", c725d8a93f.]
For minimal `𝒢` with compact unit space and any countable field:

  `A_k(𝒢)` has a faithful Sylvester matrix rank function ⟹ stably finite ⟹ `θ = [𝒢⁰]` completely non-paradoxical
  ⟺ an invariant probability measure exists.

- **Ring-level Tarski** [PASS · 638d4941b5; FOLKLORE: Tarski, Goodearl–Handelman, KMP 2502.17190 Cor 2.16].
  `simple-ring-stably-finite-iff-unit-not-paradoxical`.
- **Caution.** A state on `V(R)` is strictly weaker than a Sylvester rank function. They agree on regular rings, and
  Steinberg algebras are not regular.

### 8.2 Characteristic zero is exact, but property (T) lives only in characteristic p

- **Char 0** [PASS · 2ba472b59d, `invariant-measure-gives-rank-function-in-char-zero`; PASS · f15928d5c9,
  `char-zero-steinberg-stably-finite-iff-invariant-measure`]. For `k ⊆ ℂ`, an invariant measure gives a faithful rank
  function through the finite von Neumann algebra of `τ(f) = ∫ f|_X dμ`, so all four conditions of §8.1 are equivalent.
- **(T) only in char p** (un-tarski artifact §4.2). EJZ needs `R` finitely generated as a ring. A field finitely generated
  as a ring is finite (Artin–Tate), so every Kazhdan example lives over a finite field.
- **The Kaplansky firewall** (`measure-side-stable-finiteness-contains-char-p-kaplansky`, established). "Invariant measure
  ⟹ stably finite" for free minimal Cantor actions over `k` would prove Kaplansky's stable finiteness conjecture over `k`.
  [OPEN] `invariant-measure-gives-rank-function-any-field`.
- **Consequence.** The Kazhdan groups live exactly where "measure ⟹ matricial" is not a theorem. The measure branch must
  be witnessed by hand: Pestov's towers, Kerr–Nowak towers for free groups, Følner models for amenable groups.

### 8.3 Rank models without towers

- **Amenable acting groups** [PASS · 560decb046; `amenable-minimal-crossed-products-have-faithful-rank-models`]. Følner
  truncation of the orbit representation embeds `LC(X,k)⋊Γ` in a rank ultraproduct over any field.
- **Algebraic amenability** [unreviewed; un-open-4 dc5fe60cca, 4d7f0d1db7, a7955b459f].
  - A simple affine amenable algebra, e.g. one of subexponential growth, has a unital rank model over any field
    (`simple-amenable-affine-algebras-have-unital-rank-models`; Elek math/0203261 and math/0311376 [import]).
  - Instances: zero-entropy Pestov rings (`zero-entropy-subshift-pestov-ring-has-rank-model-by-growth`), and ℤ^d subshifts
    of subexponential complexity (`subexponential-complexity-zd-subshift-rings-have-rank-models`), including Labbé's
    Wang shift (`labbe-wang-shift-has-polynomial-pattern-complexity`).
  - [OPEN] `positive-entropy-subshift-crossed-product-is-amenable`.

### 8.4 Which acting groups turn measures into towers

[unreviewed; un-rf-beyond-free 0a7f2b4343, 5309163713.]
- **The class `𝔑`.** `Γ ∈ 𝔑` if every Cantor action with a full-support invariant measure is residually finite.
  - `𝔑` is closed under subgroups and finite-index overgroups.
  - Every virtually free group is in `𝔑` (`virtually-free-group-measure-actions-are-rf`).
  - `ℤ² ∉ 𝔑` (`z2-containing-groups-have-non-rf-measure-actions`).
  - [OPEN] `measure-rf-class-is-exactly-virtually-free-groups`.
  - [OPEN, gated like the flagship] `virtually-free-cantor-elementary-group-lef-iff-invariant-measure`.
- **Towers over every residually finite group** (`residually-finite-group-toeplitz-elementary-groups-lef-kazhdan`). Every
  f.g. infinite residually finite `Γ`, **including Kazhdan `Γ`**, has a free minimal RF Toeplitz subshift with an invariant
  measure. So `EL_n` over it is LEF and Kazhdan.
  - The free-group Toeplitz family [PASS · 10083fd646, `toeplitz-free-group-elementary-groups-are-lef-kazhdan`] is the
    case `Γ = F_r`.

### 8.5 The middle rung is realised: linear sofic, not LEF

[PASS · 560decb046; `simple-kazhdan-linear-sofic-non-lef-group-exists`.] Let `Γ_p` be the Abels–Prüfer group
(finitely presented, amenable, not residually finite), `X ⊆ 2^(Γ_p)` a free minimal subflow (Gao–Jackson–Seward [import])
and `R = LC(X,F_q)⋊Γ_p`. Then `S_N = EL_N(R)/Z` (`N ≥ 3`) is:
- infinite, finitely generated, simple and Kazhdan;
- `F_q`-linear sofic, via Følner rank models and (Σ⇐);
- not LEF, since `Γ_p ↪ S_N` (`crossed-product-group-embeds-in-projective-elementary-group`, PASS).

**Consequences.**
- `R` has rank models but is not exactly matricial. So rungs (L) and (Σ) are genuinely distinct among simple rings with
  Kazhdan groups.
- It is a live test ring for (M⇐): MF of this `S_N` would give an MF, non-LEF simple Kazhdan group.
- Soficity, hyperlinearity and MF of `S_N` are open.

## 9. Traces and operator algebras

- **MF traces** [PASS on mathematics · 10083fd646, with credit and naming GAPs applied].
  - The "corona traces" of un-traces are **Schafhauser's MF traces** (arXiv:1705.06555; Rainone–Schafhauser), a PRIOR
    concept.
  - LEF ⟹ the canonical trace is MF (folklore) ⟹ operator MF (tex l.1349 argument).
  - For an infinite LEF Kazhdan group without finite quotients, the realising map has no ucp lift.
- **Separation** [PASS (ii)–(iv) · 10083fd646]. On the paradox branch only the trivial MF trace exists; on the measure
  branch the canonical trace is MF. Item (i) was conditional on Theorem P, which has since passed (f15928d5c9). This is a
  trace-level reading of tex l.918 and LEF embeddings, not a new invariant.
- **The Kazhdan collapse** [PASS · 10083fd646; subsumed by the older `stw10-kazhdan-full-group-traces-are-qd` (Brown Mem.
  AMS 184), PRIOR Kirchberg 1994]. For a Kazhdan group, amenable trace ⟺ QD ⟺ finite-dimensional limit.
  - The ring criterion: `τ_(EL_n R)` amenable ⟺ `R` residually finite (PASS; ring step FOLKLORE).
  - So the canonical trace is blind to the dichotomy: both calibrating groups have non-amenable canonical traces.
- **Reduced C*-algebras** [unreviewed; un-reduced-cstar 3a56e40cf8].
  - **Paradox side, decided** (`measure-free-steinberg-el-n-reduced-cstar-not-mf`). For `N ≥ 2n` and every nontrivial
    quotient `Q`, `C*_r(Q)` is separable, stably finite and not MF.
  - **Measure side, three firewalls:**
    - infinite simple groups are not PMF (`minimally-almost-periodic-groups-are-not-pmf`);
    - ring-induced models carry invariant vectors for non-amenable stabilisers, so they never converge strongly
      (`ring-model-permutation-vectors-block-strong-convergence`, the Magee–de la Salle mechanism);
    - the missing step is a deterministic no-outlier theorem.
  - [OPEN] `free-group-cantor-el-n-reduced-cstar-mf-iff-invariant-measure`. Its sufficiency half implies the famous root
    `infinite-kazhdan-group-with-mf-reduced-cstar`.

## 10. The coarse face

[unreviewed; un-open-7 47fd74e1a7.]
- **RF-rigidity is free** (`un-ladder-rf-rigidity-is-free-mf-rigidity-is-dynamical`). At every rung `EL_n(R)` is perfect
  with no finite quotients, and `S` has no nontrivial map to a residually finite or linear group. So the dichotomy lives
  entirely in the gap `RF ⊊ MF`, which is why the non-MF paper states its theorems for MF targets.
- **A quasi-isometry invariant separates the ends** (`lef-infinite-simple-groups-are-qi-rigid`). A f.g. infinite simple LEF
  group is not finitely presented, hence quasi-isometric to no finitely presented group (Vershik–Gordon, PRIOR; standard
  `finitely-presented-lef-groups-are-residually-finite`, PASS · 560decb046).
  - Every measure rung is such a group.
  - The non-MF paper supplies finitely presented Kazhdan groups with no MF quotient.
- **Open.**
  - `paradox-side-elementary-group-is-finitely-presented` (via `K_2(n, L_k(1,d))`), which would move the separation inside
    the ladder.
  - `elementary-group-lef-growth-separates-subshifts`.
