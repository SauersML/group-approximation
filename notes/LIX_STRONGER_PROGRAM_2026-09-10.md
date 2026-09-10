# STW Problem LIX, the stronger theorem: unconditional Lean program (2026-09-10, lead: session 6bb5d6d1)

USER ORDER (2026-09-10): "get opus 5 team to formalize stronger version ... make sure it is
100% unconditional, no literature inputs".  This note is the single source of truth for the
program.  Read it fully before writing a line.  It extends, and never edits, the closed
program `notes/LIX_FULL_PROGRAM_2026-09-05.md` (the mod-2 answer to LIX, verified by the
Palomar Comparator on 2026-09-10 at `f6da71566`, surface `Palomar/LIXChallenge.lean`).

## 0. The target, and the wall it stops at

The manuscript family (`research/stw59-simple-ah-factorial-unitary-torsion.md`) has, for
every `n ≥ 2`, a simple unital AH algebra `A_n` with `K₁(A_n) = 0` and a unitary `v_n` whose
component has **exact order `n!`**.  Its proof is integral (K-theory Künneth, Chern character)
and its upper bound `v_n^{n!} ∈ U₀(A_n)` is Bott's `π_{2n}(U(n)) ≅ ℤ/n!`.  Neither is
formalizable without literature input, and the user forbids literature input.  So the
program formalizes the **lower bound**, which is what mod-p characteristic classes see:

```lean
/-- The stronger theorem.  For every n ≥ 2: a separable simple unital C*-algebra with a
unitary that dies in K₁ at the first stabilisation and whose powers stay outside U₀ unless
the exponent is divisible by every prime dividing n. -/
theorem exists_simple_unital_unitary_powers_outside_U0 (n : ℕ) (hn : 2 ≤ n) :
    ∃ (A : Type) (_ : CStarAlgebra A), Nontrivial A ∧ IsSimpleRing A ∧ SeparableSpace A ∧
      ∃ v : unitary A, diagOne v ∈ pathComponent 1 (unitary (CStarMat 2 A)) ∧
        ∀ k : ℕ, v ^ k ∈ pathComponent 1 (unitary A) → ∀ p : ℕ, p.Prime → p ∣ n → p ∣ k
```

Corollary (headline instance, `n = 6`): a simple unital separable `A` and `v ∈ ker κ_A` with
`v ^ k ∈ U₀(A) → 6 ∣ k`, i.e. an element of `U(A)/U₀(A)` of order divisible by 6 (or
infinite) that is trivial in `K₁`.  Corollary (every squarefree order): for every
squarefree `N` take `n = N`.  The `n = 2` instance is the existing theorem.

**Not claimed, not attempted:** `K₁(A) = 0`, exact orders, `p² ∣ k`, nuclearity, traces,
stable rank.  Mod-p cohomology cannot see `p²` (see §1.4), so `rad(n) ∣ k` is the sharp
statement this method yields.  Anyone proposing to formalize the exact order must first
produce, on paper, an unconditional proof of `2·Ση = 0 ∈ π₄(S³)`; see
`Analysis/LIXGeneratorUnitary.lean`'s module docstring for why the obvious ansätze fail.

## 1. The mathematics, as the Lean will do it

Everything is the mod-2 program with three parameters made explicit: the rank `n`, the
prime `p`, and the exponent `k`.  Read `notes/LIX_FULL_PROGRAM_2026-09-05.md` §1 first; only
the differences are stated here.

### 1.1 Objects, generic in `n`

* `S^{2n+1} := unitVectors (Fin (n+1)) ⊂ Fin (n+1) → ℂ` (sup norm, plain product, no
  `EuclideanSpace ℂ`), `S^{2n} ⊂ EuclideanSpace ℝ (Fin (2n+1))` as the equator
  `Re (x n) = 0` (`LIXLemmaSixGenerator.equatorEmb` generalised).
* Stage `i`: `r_i = n · 2^i` (`stageRank`), `Y_i = ∏_{j<i} CP(r_j)`, `X_i = S^{2n} × Y_i`,
  `H_i = ⊕_{j<i} L_j^{⊕ r_j}`, `E_i = 1^n ⊕ H_i`, `A_i = E_i M(C(X_i)) E_i`.  `rank E_i = r_i`.
  The twisted connecting maps, the limit, simplicity and separability are the existing
  arguments with `2` replaced by `n` (`Analysis/LIXConnectingMap`, `LIXLimitAlgebra`,
  `CStarSimple`, ...).  **`p ∣ r_j` for every prime `p ∣ n` and every stage** — this is the
  only place the tower's shape enters Step D.
* `F` over `S^{2n+1}`: `Fproj = 1_{n+1} − x xᴴ` (rank `n`), the complement of the tautological
  section.  The generator `u : S^{2n} → U(n)` is the seam discrepancy of the two hemisphere
  frames of `U(n+1) → S^{2n+1}` (Householder reflections through the normalised midpoint,
  exactly as at `n = 2`), so `diag(u, 1)` contracts in `U(n+1)` for free and the projection
  clutched by `u` is `Fproj`.  No `π_{2n}(U(n))` anywhere.
* `V = 1^{n+1} ⊕ H`, rank `r = n + 1 + m`, `m = Σ d_i`, over `M = S^{2n+1} × Y`; the two
  projections are `FHmat = V − s sᴴ` and `EHmat = V − e eᴴ`.

### 1.2 The constant section moves to the equator (design, owner `sp-design`, then `sp-oddside`)

At `n = 2` the constant section is `e = e₃` and the transported section's single zero sits
at `(south pole of S¹, −e₃, basepoint)` (`LIXSectionManuscript`).  `−e₃` is the suspension
point of the clutching coordinate, and a degree-`k` map of the sphere that preserves the
hemispheres is a cone at the suspension points, so with `e = e₃` the `k`-th power's zeros
could never be local homeomorphisms.  **Take `e = e₁`** (any unit vector with
`Re (e n) = 0`): `EHmat` changes by a constant unitary, Lemma 2 is unchanged, and the zero
moves to `x = −e₁` on the equator.  `sp-design` must confirm from `LemmaTwoZero.lean` that
the zero of the transported section for abstract block data `(a, b, c)` is where `b = −a`.

### 1.3 Powers: Step C with `k` zeros (design, owners `sp-design`, `sp-powers`, `sp-oddside`)

For `v^k ∉ U₀(A_j)` the chain is:

1. **Eckmann–Hilton on `U(n)`-valued maps of `S^{2n}`.**  `u^k` (pointwise power) and
   `u ∘ ψ_k` are homotopic, where `ψ_k : S^{2n} → S^{2n}` is an explicit `k`-fold map (§1.3.2).
   Formal shape: `IsDiscUnitary`-style — exhibit `u^k · (u ∘ ψ_k)⁻¹ ∈ U₀(C(S^{2n}, U(n)))` as a
   unitary over the disc restricting to it on the sphere.  (owner `sp-powers`)
2. **Gauge lemma.**  If `a ∈ U₀` (extends over the northern hemisphere) then
   `clutch(a·b) ≅ clutch(b)` (change the northern trivialisation by the extension; this is
   `LIXClutching`'s seam trick and needs no square root).  Hence `clutch(u^k) ≅ clutch(u ∘ ψ_k)`.
   (owner `sp-powers`; check whether `LIXClutching` already has it in this generality)
3. **Naturality of clutching.**  `clutch(u ∘ ψ_k) = (Σψ_k)^* clutch(u) = (x ∘ Σψ_k)^⊥` where
   `Σψ_k : S^{2n+1} → S^{2n+1}` is the suspension (acts on the equatorial coordinates, fixes
   the clutching coordinate `Re (x n)`).  (owner `sp-powers`)
4. **Step C with `k` zeros.**  With `b = x ∘ Σψ_k` and `a = e₁` the transported section
   vanishes exactly at `{south} × (Σψ_k)^{-1}(−e₁) × {basepoint}`, which is `k` equatorial
   points at each of which `Σψ_k` is a local homeomorphism (§1.3.2).  Then
   `γ_r(W_g) = j^*(σ^* U) = Σ_i j^*(loc_i)` by excision to `k` disjoint balls, and each
   `j^*(loc_i)` is the one-zero computation already in the tree (`LIXStepCOdd*`), transported
   along the rotation `ρ^i` (§1.3.2): `j^*(loc_i) = (ρ^{-i})^*(j^*(loc_0)) = j^*(loc_0)` by
   naturality of `j` and ABSOLUTE homotopy invariance (`ρ` is isotopic to the identity).
   Hence `γ_r(W_g) = k · c₀` with `c₀ ≠ 0`, so `γ_r(W_g) ≠ 0` whenever `p ∤ k`.
   **Over `F_p` with `p` odd this is where signs would enter; the `ρ`-symmetry is what makes
   every local contribution literally equal, so no local degree is ever computed.**
   (owner `sp-oddside`, after `sp-design` signs off)

#### 1.3.2 The `k`-fold map `ψ_k` (design, owner `sp-design`)

Requirements: (i) `ψ_k : S^{2n} → S^{2n}` continuous; (ii) `ψ_k ∘ ρ = ψ_k` for a rotation
`ρ` of order `k` (a rotation by `2π/k` in a plane not containing `e₁`, restricted to the
equator sphere); (iii) `ψ_k^{-1}(−e₁) = {q₀, ρ q₀, …, ρ^{k-1} q₀}` and `ψ_k` is a local
homeomorphism at each, with `ψ_k = ρ^{-i} ∘ (ψ_k near q₀)` near `ρ^i q₀`; (iv) `u ∘ ψ_k` is
homotopic to `u^k` (Eckmann–Hilton needs `ψ_k` to be the `k`-fold pinch sum of the identity
up to homotopy; the cleanest is to DEFINE `ψ_k` as an explicit `ρ`-equivariant pinch sum and
prove the pointwise product of the `k` summands is homotopic to the pinch sum).  Deliver the
formula, the zero count, and the equivariance as Lean-precision lemmas.  Model-test the
zero count numerically before writing anything.

### 1.4 Step D mod `p`, uniform in the stage (design, owner `sp-design`, then `sp-evenside`)

Over `F_p`: `H^*(N) ⊇ H^*(Y)[z]/(z²)` in even degrees, `z = t x`, `deg z = 2n+2`,
`γ(W) = γ(V)(1 + z b)`, `b ∈ H^*(Y; F_p)` unknown.  Available relations, and ONLY these:
the total reduced power `P = Σ P^i` is a ring homomorphism (Cartan), `P(h) = h + h^p` on
degree-2 classes, `P(z) = z`, instability `P^i = 0` below degree `2i`, and the Wu relations
`P(γ_j(W)) = E_j(γ(W))` **for each `j` separately** (the universal polynomials `E_j` with
`P(e_j) = E_j(e)`; the total-class identity alone is too weak — it lost the calibration case).
The needed conclusion is `γ_r(W) = 0`, i.e. `z·(b γ(V))_{2m} = 0`.

**Model test** (`scratch/lix_modp_fast.py` on MSI, lead, 2026-09-10; source in this session's
scratchpad `sp/`): with `p ∣ n`, the relations force `γ_r(W) = 0` at every stage tested;
with `p ∤ n` they generally do not, and the controls behave as Bott requires.

| n | p | d (stages) | forced? |
|---|---|---|---|
| 2 | 2 | [2], [2,4], [2,4,8] | yes (calibration: the existing proof) |
| 2 | 3 | [3], [] | **no** (must be no: Bott gives an allowable bundle with Chern number 2) |
| 3 | 3 | [3], [6], [3,6], [3,6,12] | yes |
| 3 | 2 | [2], [6] | no |
| 4 | 2 | [2], [4], [8] | yes |
| 4 | 3 | [3], [4], [4,8] | no |
| 5 | 5 | [5] | yes |
| 6 | 2 | [6], [12], [24], [6,12], [12,24] | yes |
| 6 | 3 | [6], [12], [24], [6,12], [12,24] | yes |
| 6 | 5 | [6] yes, [12], [6,12], [12,24] | **no** |
| 6 | 7 | [6], [6,12] | no (control: 7 ∤ 6!) |
| 7 | 7 | [7], [7,14], [14,28] | yes |
| 7 | 2,3,5 | [7,14] | no |
| 10 | 2,3,5 | [10,20] | yes |
| 10 | 7 | [10], [10,20] | no |
| 11 | 11 | [11], [11,22] | yes |

Conjecture the lanes must turn into a proof: **for every prime `p ∣ n` and every stage,
the relations force `γ_r(W) = 0`.**  The expected mechanism is the mod-2 one: `p ∣ d_i`
makes `γ(V) = ∏(1 + h_i^p)^{d_i/p}` supported in degrees `≡ 0 mod 2p` (Frobenius), and the
Wu relations read on the `z`-part, with instability, kill the coefficients `b` in the
complementary residues.  `sp-design` derives the uniform argument from the model's
certificates (print which relation kills which coefficient), states it as a finite list of
lemmas over an abstract `F_p`-algebra `H^*(Y)[z]/(z²)`, and model-tests every lemma.
A proof that works stage by stage but not uniformly is NOT acceptable: the limit needs
all stages.

### 1.5 Coefficients and operations (owners `sp-coeff`, `sp-steenrod`)

* The vendored cochain layer is generic in the coefficient ring
  (`ThirdParty/.../CupProduct.lean: singularCochainGroup (R : Type) [CommRing R]`);
  `cohomologyZMod2` is an `abbrev` specialisation.  `CharClass/CohomologyBasic.lean`'s
  `Hmod2` pins `ZMod 2`, and 230 `CharClass` files name `ZMod 2`.  The plan is a
  coefficient parameter `K` (a field, or `ZMod p` with `[Fact p.Prime]`) through the layers
  that never use `1 = -1`: cohomology basic/assoc/pull, Mayer–Vietoris, relative pairs and
  excision, Leray–Hirsch, Chern classes via Leray–Hirsch, projective bundles, Thom class,
  Gysin.  Graded commutativity is not provided at `F₂` and must not be assumed at `F_p`;
  Chern classes have even degree and commute regardless.  The `F₂` instance must keep
  building at every landing: the LIX answer is a verified artifact and stays green.
* The odd-primary Steenrod powers `P^i` at cochain level, with naturality, `P^0 = id`,
  Cartan formula (total `P` multiplicative), instability (`P^i = 0` below degree `2i`,
  `P^{q/2} = p`-th power on degree `q` even), `P(h) = h + h^p` on degree 2.  The `F₂` tree
  builds `Sq` from cup-`i` products (`SteenrodSquare.lean`) and the Cartan formula by acyclic
  models (`Cartan*.lean`); for odd `p` the cup-`i` route does not exist and the construction
  is the `ℤ/p`-equivariant diagonal approximation on the `p`-fold tensor power (the
  standard `W ⊗ C(X) → C(X)^{⊗p}` over the free `ℤ[ℤ/p]`-resolution `W`), from which `P^i`
  are the classes of `u^{⊗p}` paired with the generators of `W` in the right degrees, with
  the mod-`p` normalisation.  This is the hardest lane and it is on the critical path.
  `sp-steenrod` writes the construction plan first (which acyclic-models statements are
  needed, which the tree already has, what normalisation constant appears and why it is a
  unit mod `p`) and gets it reviewed by `sp-design` before authoring.
* Wu relations for `P^i` on mod-`p` Chern classes follow from the splitting principle
  exactly as `Wu.HasSplitting` does at `F₂`; the universal polynomials `E_j` are the
  elementary symmetric functions of `y + y^p`.

### 1.6 The endpoint (owner: lead, then `sp-endpoint`)

`Analysis/LIXEndpointStatement.lean`'s `HasK1InjWitness` becomes a `k`-indexed family; the
C*-side bridge `LIXLemmaSixCor4.climb_genUnitary_notMem` becomes
`climb_genUnitary_pow_notMem (k) (hk : ¬ p ∣ k)`; `LemmaTwoHolds` becomes `LemmaTwoHolds n p k`
(`¬ ContinuousMvNEquiv (FHmat_k) EHmat` at every stage, `FHmat_k` built from `x ∘ Σψ_k`).
The Palomar surface is a third configuration `Palomar/comparator-lix-strong.json` with a
Mathlib-only challenge stating the `n = 6` corollary and the general theorem.

## 2. Lanes (all `model: opus`, named; resume with SendMessage to the name)

| lane | clone / cores | owns | first deliverable |
|---|---|---|---|
| `sp-design` | spare1 / 96-103 | this note §1.2–1.4 as theorems; every model test | uniform Step D proof for `p ∣ n`; `ψ_k` design; sign-off gate for the Lean lanes |
| `sp-tower` | cs-stages / 88-95 | `Analysis/LIX*` generic in `n` | `stageRank n i`, `Fproj n`, seam generator for `U(n+1) → S^{2n+1}`, `diag(u,1) ∈ U₀`, tower, limit, simplicity, separability at general `n` with the `n = 2` instance unchanged |
| `sp-coeff` | cs-endpoint / 64-71 | `CharClass` coefficient parameter | `Hmod K`, cup/pull/MV/relative/excision/LH/Chern/Thom/Gysin over a field `K`, `F₂` instance green |
| `sp-steenrod` | cs-limit / 72-79 | odd-primary `P^i` | construction plan reviewed, then the operations with Cartan + instability + `P(h) = h + h^p` |
| `sp-powers` | cs-simplicity / 80-87 | §1.3 items 1–3 | Eckmann–Hilton over `U(n)`, gauge lemma, clutching naturality along `Σψ_k` |
| later: `sp-oddside`, `sp-evenside`, `sp-endpoint` | | §1.3.4, §1.4, §1.6 | after `sp-design` signs off |

Ownership is by file: a lane creates files under its own prefix and edits existing files
only when the table says it owns them.  Two lanes never edit one file; ask the lead.

## 3. Protocol (binding)

* **Lean only after solving.**  No Lean is authored for a statement whose proof is not
  written in this note or in the lane's report at the precision of a lemma list, and
  model-tested where it is numeric.  `sp-design` gates §1.2–1.4.
* **Builds.**  `scratchpad sp/laneprobe.sh <clone> <Module...>` (path given in the launch
  message): syncs the shared local tree into the lane's private warm clone on MSI and builds
  there on the lane's 8-core range under `nice`.  Never build locally.  Never use another
  lane's clone.  Never use `/tmp` on the node.  Do not start a second probe while one runs
  (the helper serialises with `flock`; queueing is wasted wall-clock).  A probe that takes
  more than 15 minutes is a signal to cut the import closure, not to wait.
* **No `sorry` lands.**  Author with `sorry` only inside a file that is not imported by
  anything, and say so in the report.  `#print axioms` on every endpoint-facing theorem:
  `[propext, Classical.choice, Quot.sound]`, nothing else, ever.
* **Statements before proofs.**  Land the statement of each obligation as a `Prop` with a
  docstring saying who discharges it, then discharge.  A hypothesis used once is an over-ask.
* **Landing.**  Lanes do not commit or push.  The lead commits and pushes the shared tree
  regularly; a lane's report says which files are green and at which job count.
* **Reports.**  `notes/lix-stronger-lane-reports/<lane>.md`, four sections (GREEN with job
  counts / AUTHORED, UNVERIFIED / NEEDS / TRAPS), kept current.  Cross-lane traps go to
  `notes/lix-lane-reports/FLEET_TRAPS.md` (append only).  Read it before a second failed
  probe on the same error.
* **MSI.**  8 cores per lane, `nice -n 5`, warm clones only, no job spam, kill hung `lake`
  processes you started (`pkill -u sauer354 -f "lake build <your module>"`), never touch
  other users' processes.
* **Idiom.**  `notes/lix-lane-reports/FLEET_TRAPS.md` and the memory files named in the
  launch message are the accumulated Lean traps of this tree; the mod-2 files are the
  template for every construction.
