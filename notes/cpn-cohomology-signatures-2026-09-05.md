# `ℂP^n` foundations: published signatures (lane `found-cpn-cohomology`)

Owner: lane `found-cpn-cohomology`.
Files owned: `GroupApproximation/AlgTop/ComplexProjective*.lean`,
`GroupApproximation/AlgTop/PuncturedNormedSphere.lean`.
Consumers: `found-chern-classes`, `found-ktheory-bott`, `found-mapping-torus-parity`,
`found-euler-class`, `lix-clutching`, `lix-obstruction`.

Target: manuscript
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md` §2,
equation (2.1),

```
H^*(Y; Z) = Z[h_1,...,h_l]/(h_1^{d_1+1},...,h_l^{d_l+1}),  |h_j| = 2,  Y = prod_j CP^{d_j}
c_m(H) = prod_j h_j^{d_j},   |<c_m(H), [Y]>| = 1.
```

**The model is not mine.** It lives in
`GroupApproximation/Analysis/LIXProjectiveSpaceModel.lean` (lane `lix-spaces`),
namespace `GroupApproximation.STW59`:

```lean
def cpSet (d : ℕ) : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  {q | qᴴ = q ∧ q * q = q ∧ q.trace = 1}
abbrev CP (d : ℕ) := ↥(cpSet d)
```

with the subspace topology of the product topology on matrices. I authored a duplicate
of this before theirs appeared and deleted it; there is exactly one model in the repo.
Everything below lives in namespace `GroupApproximation.AlgTop.CPn` and adds no
competing definition.

`CP d` is complex projective `d`-space: `CP 0` is a point and `CP d` has real dimension
`2d`. **Do not change this indexing**; every cohomology statement below is keyed to it.

## Part A — authored, unconditional, no dependency on any lane but `lix-spaces`

Status: all eight modules pushed, none yet compiled — `LIXProjectiveSpaceModel.lean` has
been red all afternoon and every module of mine imports it. See "Build state" below.

### A.0 Entry calculus (`ComplexProjectiveBasic.lean`)

```lean
abbrev CPn.entry (x : CP d) (a b : Fin (d + 1)) : ℂ := (x : Matrix _ _ ℂ) a b

/-- rank one, as the vanishing of every 2x2 minor -/
theorem CPn.minor {q} (hq : q ∈ cpSet d) (a b j) : q a j * q j b = q j j * q a b
theorem CPn.entry_minor (x : CP d) (a b j) :
    entry x a j * entry x j b = entry x j j * entry x a b
theorem CPn.entry_sum_mul (x : CP d) (a b) : (∑ c, entry x a c * entry x c b) = entry x a b
theorem CPn.entry_symm (x : CP d) (a b) : entry x a b = star (entry x b a)
theorem CPn.entry_conj (x : CP d) (a b) : (starRingEnd ℂ) (entry x b a) = entry x a b
theorem CPn.entry_diag (x : CP d) (j) : entry x j j = ((∑ k, ‖entry x k j‖ ^ 2 : ℝ) : ℂ)
theorem CPn.entry_col_eq_zero (x) (hj : entry x j j = 0) (c) : entry x c j = 0
theorem CPn.entry_row_eq_zero (x) (hj : entry x j j = 0) (c) : entry x j c = 0
theorem CPn.ext {x y : CP d} (h : ∀ a b, entry x a b = entry y a b) : x = y
theorem CPn.continuous_entry (a b) : Continuous fun x : CP d => entry x a b
def CPn.basePoint (d : ℕ) : CP d
```

`CPn.minor` is the single fact every downstream computation runs on. It is one step from
`STW59.eq_rankOneProj_of_trace_one`, but unlike that existential it is usable as a
rewrite: on `{q j j ≠ 0}` it recovers every entry of `q` from its `j`-th column and row.

### A.1 The affine chart (`ComplexProjectiveChart.lean`)

```lean
def CPn.chartVec (w : Fin d → ℂ) : Fin (d + 1) → ℂ := Fin.cons 1 w
def CPn.chartAt (w : Fin d → ℂ) : CP d                       -- [1 : w_1 : ... : w_d]
def CPn.chartInv (x : CP d) : Fin d → ℂ                      -- i ↦ entry x i.succ 0 / entry x 0 0
def CPn.chartSet (d : ℕ) : Set (CP d) := {x | entry x 0 0 ≠ 0}

theorem CPn.chartAt_entry (w) (a b) :
    entry (chartAt w) a b = chartVec w a * star (chartVec w b) / ((sqNorm (chartVec w) : ℝ) : ℂ)
theorem CPn.isOpen_chartSet : IsOpen (chartSet d)
theorem CPn.chartInv_chartAt (w) : chartInv (chartAt w) = w
theorem CPn.chartAt_chartInv (x) (hx : entry x 0 0 ≠ 0) : chartAt (chartInv x) = x
def CPn.chartHomeo (d : ℕ) : (Fin d → ℂ) ≃ₜ ↥(chartSet d)
theorem CPn.chartAt_zero (d : ℕ) : chartAt (0 : Fin d → ℂ) = basePoint d
```

No square root survives: `CPn.rankOneProj_normalize` shows the normalization by
`Real.sqrt (sqNorm u)` cancels, so the entries are *rational* in `w` and `star w`, which
is what makes continuity free. `chartAt_chartInv` is exactly `CPn.minor` at `j = 0`.

### A.2 The hyperplane (`ComplexProjectiveHyperplane.lean`)

```lean
def CPn.incl (x : CP d) : CP (d + 1)                     -- pad by a zero row and column
theorem CPn.continuous_incl, CPn.injective_incl
theorem CPn.isClosedEmbedding_incl : Topology.IsClosedEmbedding (incl (d := d))
theorem CPn.range_incl : Set.range (incl (d := d)) = {y : CP (d + 1) | entry y 0 0 = 0}
theorem CPn.chartSet_eq_compl_range_incl : chartSet (d + 1) = (Set.range incl)ᶜ
def CPn.deincl (y : CP (d + 1)) (hy : entry y 0 0 = 0) : CP d
theorem CPn.incl_deincl (y) (hy) : incl (deincl y hy) = y
```

So `ℂP^{d+1}` is `ℂP^d` with one open `2(d+1)`-cell attached. Iterating gives the
filtration `ℂP^0 ⊂ ℂP^1 ⊂ ⋯ ⊂ ℂP^n` with exactly one cell in each even dimension
`0, 2, …, 2n` and none in odd dimensions — **mandate item 1**. Since every cell is
even-dimensional, every cellular boundary map is a map out of a group into `0`, hence
zero; the cellular chain complex has zero differential. That is why `ℂP^n` is far cheaper
than the `RP^n` precedent in `ThirdParty/HamSandwich/SphereOddDegree/`.

### A.3 The deformation off the base point (`ComplexProjectivePuncture.lean`)

```lean
/-- weighted idempotency, for ARBITRARY weights -/
theorem CPn.weighted_sum (x : CP d) (δ : Fin (d + 1) → ℂ) (a b) :
    (∑ c, δ c * (entry x a c * entry x c b)) = (∑ c, δ c * entry x c c) * entry x a b

def CPn.rad (x : CP d) : ℝ                              -- entry x 0 0, as a real in [0,1]
theorem CPn.rad_eq_one_iff {x : CP d} : rad x = 1 ↔ x = basePoint d
def CPn.punctured (d : ℕ) : Set (CP (d + 1)) := {x | x ≠ basePoint (d + 1)}
def CPn.scale (p : I × ↥(punctured d)) : CP (d + 1)
theorem CPn.continuous_scale, CPn.scale_zero, CPn.scale_one_mem_range_incl,
        CPn.scale_of_entry_zero_zero_eq_zero
```

`weighted_sum` is the engine: with `δ c = (1-t)²` or `1` according to whether `c = 0`, it
is simultaneously the idempotent law and the trace computation for the renormalized
scaled matrix. Its proof is `CPn.minor` four times plus cancellation of a nonzero
diagonal entry — no rank theorem, no spectral theorem, no square roots.

`scaleTrace t x = (1-t)² rad x + (1 - rad x) ≥ 1 - rad x > 0` for **every real `t`**;
the unit interval is needed only to have a homotopy, never for well-definedness.

### A.4 The homotopy equivalence (`ComplexProjectivePunctureRetract.lean`)

```lean
def CPn.retract (x : ↥(punctured d)) : CP d
def CPn.inclP (z : CP d) : ↥(punctured d)
theorem CPn.retract_inclP (z : CP d) : retract (inclP z) = z          -- on the nose
def CPn.punctureHomotopyEquiv (d : ℕ) : ContinuousMap.HomotopyEquiv ↥(punctured d) (CP d)
```

`CPn.rad_scale_lt_one` is what keeps the homotopy inside the punctured space:
`rad (scale t x) = (1-t)² rad x / τ < 1` exactly, not merely approximately.

### A.5 The Mayer–Vietoris cover (`ComplexProjectiveCover.lean`)

```lean
theorem CPn.union_eq_univ (d : ℕ) : chartSet (d + 1) ∪ punctured d = Set.univ
theorem CPn.inter_eq (d : ℕ) :
    chartSet (d + 1) ∩ punctured d = {x | entry x 0 0 ≠ 0 ∧ x ≠ basePoint (d + 1)}
theorem CPn.isOpen_inter (d : ℕ)
theorem CPn.chartAt_eq_basePoint_iff {w} : chartAt w = basePoint d ↔ w = 0
def CPn.chartPuncturedHomeo (d : ℕ) :
    {w : Fin d → ℂ // w ≠ 0} ≃ₜ ↥(chartSet d ∩ {x : CP d | x ≠ basePoint d})
theorem CPn.eq_basePoint_zero (x : CP 0) : x = basePoint 0
instance CPn.subsingleton_CP_zero : Subsingleton (CP 0)
```

### A.6 The intersection is a sphere (`PuncturedNormedSphere.lean`, `ComplexProjectiveSphere.lean`)

```lean
-- model-independent, imports only Mathlib
def AlgTop.puncturedHomotopyEquivSphere (E) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.HomotopyEquiv ↥({0}ᶜ : Set E) ↥(Metric.sphere (0 : E) 1)
theorem AlgTop.finrank_pi_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n
def AlgTop.complexToEuclidean (n : ℕ) : (Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * n))
def AlgTop.complexPuncturedHomotopyEquivSphere (d : ℕ) :
    ContinuousMap.HomotopyEquiv {w : Fin (d + 1) → ℂ // w ≠ 0}
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * (d + 1)))) 1)

-- model-dependent
def CPn.interHomotopyEquivSphere (d : ℕ) :
    ContinuousMap.HomotopyEquiv
      ↥(chartSet (d + 1) ∩ {x : CP (d + 1) | x ≠ basePoint (d + 1)})
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * (d + 1)))) 1)
theorem CPn.contractibleSpace_chartSet (d : ℕ) : ContractibleSpace ↥(chartSet d)
```

**Net effect.** Every term of the Mayer–Vietoris sequence for `ℂP^{d+1}` is identified:
`U` contractible, `V ≃ₕ ℂP^d`, `U ∩ V ≃ₕ S^{2d+1}`, base case `ℂP^0` a point. The only
missing ingredient is the sequence itself.

## Part B — blocked on `found-cohomology-ring`

Their contract is `notes/algtop-foundation-plan-2026-09-05.md`. It is a good contract and
I am coding against it, but **it contains no Mayer–Vietoris for cohomology**: its §0 cites
the vendored `mvHomologyIso` for the singular *chain* complex, and §3–§6 give no long
exact sequence in `cohomology R X n` for an open cover. Without that, mandate items 2–5
cannot start. Flagged to them with the exact signatures; offered to build it myself by
dualizing `mvShortExact` (`ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/
MayerVietoris.lean:98`) with `HomologicalComplex.opFunctor` + `linearYoneda`, which is
exact here because the complexes are degreewise free. **Unclaimed as of this writing.**

Their API that I will consume, verbatim from their plan:
`cohomology R X n`, `cohomologyℤ X n`, `cohPullback`, `cohPullback_eq_of_homotopy`,
`cup`, `cohPullback_cup`, `cohCast`, `sphereGen`, `spherePairing`,
`sphere_cohomology_isZero`, `FreeCohomology`, `cross`, `kunnethIso`.

### B.1 Item 2 — additive cohomology of `ℂP^d`

```lean
theorem CPn.cohomology_even_iso (d k : ℕ) (hk : k ≤ d) : Nonempty (H (2 * k) (CP d) ≃+ ℤ)
theorem CPn.cohomology_odd_isZero (d j : ℕ) (hj : Odd j) : Subsingleton (H j (CP d))
theorem CPn.cohomology_high_isZero (d j : ℕ) (hj : 2 * d < j) : Subsingleton (H j (CP d))
```

Proof route, fixed and fully prepared by Part A: reduced Mayer–Vietoris for
`CPn.union_eq_univ`, giving `H~^k(ℂP^{d+1}) ≅ H~^k(ℂP^d)` for `k ≤ 2d`,
`H~^{2d+1}(ℂP^{d+1}) = 0`, `H~^{2d+2}(ℂP^{d+1}) ≅ H~^{2d+1}(S^{2d+1}) ≅ ℤ`.

### B.2 Item 3 — the ring `ℤ[h]/(h^{d+1})`

```lean
def CPn.h (d : ℕ) : H 2 (CP d)
theorem CPn.h_pow_ne_zero (d k) (hk : k ≤ d) : CPn.h d ^ k ≠ 0
theorem CPn.h_pow_spans (d k) (hk : k ≤ d) (c : H (2 * k) (CP d)) : ∃ m : ℤ, c = m • (h d ^ k)
theorem CPn.h_pow_succ_eq_zero (d : ℕ) : CPn.h d ^ (d + 1) = 0
theorem CPn.incl_h (d : ℕ) : (CPn.incl (d := d))^* (CPn.h (d + 1)) = CPn.h d
def CPn.cohomologyRingEquiv (d : ℕ) :
    (⨁ j, H j (CP d)) ≃+* (Polynomial ℤ ⧸ Ideal.span {Polynomial.X ^ (d + 1)})
```

`CPn.incl_h` is the load-bearing step and it needs **naturality of the cup product**
(`cohPullback_cup`), which their plan does provide.

### B.3 Item 4 — products, and (2.1)

```lean
abbrev CPProd {ι : Type} [Fintype ι] (dd : ι → ℕ) : Type := ∀ j : ι, CP (dd j)
def CPProd.h {ι} [Fintype ι] (dd : ι → ℕ) (j : ι) : H 2 (CPProd dd)
def CPProd.topClass {ι} [Fintype ι] (dd : ι → ℕ) :
    H (2 * ∑ j, dd j) (CPProd dd) := ∏ j, (CPProd.h dd j) ^ (dd j)

theorem CPProd.cohomology_top_iso (dd) : Nonempty (H (2 * ∑ j, dd j) (CPProd dd) ≃+ ℤ)
theorem CPProd.topClass_ne_zero (dd) : CPProd.topClass dd ≠ 0
theorem CPProd.topClass_spans (dd) (c) : ∃ m : ℤ, c = m • CPProd.topClass dd
theorem CPProd.cohomology_odd_isZero (dd) (n) (hn : Odd n) : Subsingleton (H n (CPProd dd))
theorem CPProd.cohomology_free (dd) (n) : Module.Free ℤ (H n (CPProd dd))
```

`topClass_spans` + `topClass_ne_zero` **is** (2.1): the top monomial generates
`H^{2m}(Y;ℤ) ≅ ℤ`, so its pairing with the fundamental class is a unit. Note this form
needs **no fundamental class at all**, which is a simplification of the manuscript worth
taking; if `found-cohomology-ring` supplies one I will add the `±1` pairing statement too.

### B.4 Item 5 — products with spheres (torsion-freeness)

```lean
abbrev LIXBase {ι} [Fintype ι] (dd : ι → ℕ) : Type := Sph 1 × Sph 5 × CPProd dd
theorem LIXBase.cohomology_free (dd) (n) : Module.Free ℤ (H n (LIXBase dd))
theorem LIXBase.cohomology_finite (dd) (n) : Module.Finite ℤ (H n (LIXBase dd))
```

`Module.Free ℤ M` for finitely generated `M` is exactly torsion-freeness, which is what
Lemma 3 uses to identify integral coefficients from a rational computation. Both sides of
the Künneth are free, so this is a corollary rather than a separate argument.
`found-mapping-torus-parity` additionally wants the explicit basis
`t^{ε₀} x^{ε₁} ∏_j h_j^{b_j}`, `ε ∈ {0,1}`, `b_j ≤ d_j`; I will state it as a `Basis` once
the Künneth name is fixed.

## Build state and traps recorded

Nothing in Part A has compiled yet. Two fleet-mutex slots were spent discovering that
`LIXProjectiveSpaceModel.lean` was red (round 1: `continuous_finset_sum`, a deprecated
alias, and `Continuous.matrix_trace`, which does not exist at pin 81a5d257; round 2:
an unused binder `hq`, and a `simp made no progress` caused by putting a `by simp only`
block into `isClosed_eq`'s first argument, whose implicit `f` is still a metavariable
when the block runs).

Offline checks that did pay off, and are worth other lanes' time:

1. **Deprecated aliases are hard errors** here (`-DwarningAsError=true`). Diff every
   identifier against `git grep "deprecated (since" 81a5d257` — there are 1986 of them.
2. **`open Matrix` and protected names.** `Matrix.star_mul` is a deprecated alias,
   `Matrix.sum_mul` and `Matrix.zero_mul` are live, and all three are `protected`, so
   `open Matrix` does *not* expose them unqualified. Bare `star_mul` still resolves to the
   root `StarMul`-exported lemma. Check `protected` before assuming a collision.
3. **The unused-variable linter is a hard error.** Scan every explicit binder and count
   its occurrences in its own declaration; one occurrence means only the binding site.
   This found `scaleTrace_pos`'s `ht : 0 ≤ t` and `ht1 : t ≤ 1` in my own file — and they
   were not merely unused but unnecessary, since `(1-t)²` is a square.
4. **"Exists at the pin" is not "reachable from your imports."** My chain imported only
   `LIXProjectiveSpaceModel`, whose import list is deliberately narrow and contains
   neither `Real.sqrt` nor `unitInterval` nor the homotopy files. Audit against your own
   import closure, not against Mathlib as a whole.
5. **Never put a `by` block starting with `simp`/`rw` in an argument position whose type
   is still a metavariable.** Hoist it into a `have` with an explicit type.
