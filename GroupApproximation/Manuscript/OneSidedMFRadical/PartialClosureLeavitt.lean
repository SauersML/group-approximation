import GroupApproximation.Leavitt.RootDetectionBinary
import GroupApproximation.Leavitt.ElementaryTransvectionExtraction

/-!
# Five printed coefficient calculations of `prop:simple`, as closed sentences

`non_mf_groups_exist.tex`, the proof that the rank-twelve elementary group over
`L_{𝔽₂}(1,2)` is simple, runs five calculations that the tree proves only
*inside* larger proofs:

* "and `yx = d s₀ t₁ c = 0` would imply `s₀t₁ = (cwd)(s₀t₁)(cwd) =
  (cw)((ds₀)(t₁c))(wd) = 0`" — a `calc` block inside the second conjunct of
  `exists_reversing_zero_product`;
* "To obtain `\eqref{eq:coefficient-separation}`, choose factorizations
  `c_r r d_r = 1`, `e_d d_r f_d = 1`, `e_s s f_s = 1`, `e_t (c_r r) f_t = 1`"
  — four proof-internal `obtain`s inside `exists_annihilate_preserve_reverse`,
  together with the nonvanishing facts `d_r ≠ 0` and `c_r r ≠ 0` that justify
  applying two-sided division to them;
* "Thus for some `i ≠ j` and `a ∈ R`, conjugation by `g` sends `e_{ij}(a)` to
  `e_{ij}(y)` with `y ≠ a`" — the internal `ha` of the diagonal branch of
  `RootDetectionBinary.exists_elGen_mem_of_diagonal`;
* "Thus the `(i,m)` entry of the defect in `\eqref{eq:row-unipotent-zero-inverse}` is
  nonzero" — the internal `hvm` of `exists_elGen_mem_of_inv_entry_zero`;
* "Again `AB = 0`, because its potentially nonzero coefficient contains `arb`"
  — the internal `hAB` of `exists_elGen_mem_of_annihilating_coefficients`.

Each is restated here as a named `Prop` whose quantifiers and hypotheses live
*inside* the statement, so that `#audit_closed_axioms` (which throws on any
leading binder) applies, and proved.  Nothing new is assumed: every hypothesis
is one the manuscript itself prints at that point in the proof.  The two
hypotheses that are properties of the coefficient ring — two-sided division and
triviality of central units — are additionally discharged at
`L_{𝔽₂}(1,2)` (`...AtBinaryLeavitt`), so no statement below is vacuous.

No theorem from the literature is an input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open ElementarySimplicity
open scoped commutatorElement

/-! ## The reversed product, and why it cannot vanish

`non_mf_groups_exist.tex`: the paragraph proving that for every `w ∈ R` there
are `x, y` with `xwy = 0` and `yx ≠ 0`, in the branch `w ≠ 0` with `cwd = 1`,
`x = t₁c`, `y = ds₀`. -/

/-- **"and `yx = d s₀ t₁ c = 0` would imply
`s₀t₁ = (cwd)(s₀t₁)(cwd) = (cw)((ds₀)(t₁c))(wd) = 0`."**

The three printed equalities of the display, followed by the printed
implication itself.  The manuscript reads the implication contrapositively
(`s₀t₁ ≠ 0`, hence `yx ≠ 0`); what is stated here is the implication the
sentence actually prints, so that the reader can check the display line by
line.  No nontriviality of `R` is needed: that is used only to know
`s₀t₁ ≠ 0`, which is a *different* sentence. -/
def PrintedReversedProductVanishingImplication : Prop :=
  ∀ (S : Type) [Ring S] (L : LeavittFamily S) (w c d : S), c * w * d = 1 →
    (d * L.s0) * (L.t1 * c) = d * L.s0 * L.t1 * c ∧
      L.s0 * L.t1 = (c * w * d) * (L.s0 * L.t1) * (c * w * d) ∧
      (c * w * d) * (L.s0 * L.t1) * (c * w * d)
        = (c * w) * ((d * L.s0) * (L.t1 * c)) * (w * d) ∧
      ((d * L.s0) * (L.t1 * c) = 0 → L.s0 * L.t1 = 0)

/-- Closed proof of the printed implication and its display. -/
theorem manuscriptPrintedReversedProductVanishingImplication :
    PrintedReversedProductVanishingImplication := by
  intro S _ L w c d hcwd
  have hmid : (c * w * d) * (L.s0 * L.t1) * (c * w * d)
      = (c * w) * ((d * L.s0) * (L.t1 * c)) * (w * d) := by noncomm_ring
  have hone : L.s0 * L.t1 = (c * w * d) * (L.s0 * L.t1) * (c * w * d) := by
    rw [hcwd, one_mul, mul_one]
  have hassoc : (d * L.s0) * (L.t1 * c) = d * L.s0 * L.t1 * c := by noncomm_ring
  refine ⟨hassoc, hone, hmid, ?_⟩
  intro hyx
  calc L.s0 * L.t1
      = (c * w * d) * (L.s0 * L.t1) * (c * w * d) := hone
    _ = (c * w) * ((d * L.s0) * (L.t1 * c)) * (w * d) := hmid
    _ = 0 := by rw [hyx, mul_zero, zero_mul]

/-! ## Coefficient separation: the four printed factorizations

`non_mf_groups_exist.tex`: "To obtain `\eqref{eq:coefficient-separation}`,
choose factorizations `c_r r d_r = 1`, `e_d d_r f_d = 1`, `e_s s f_s = 1`,
`e_t (c_r r) f_t = 1`, apply the preceding construction to `w = e_t f_d`, and
set `a = f_s x e_t c_r`, `b = d_r f_d y e_s`." -/

/-- **"choose factorizations `c_r r d_r = 1`, `e_d d_r f_d = 1`,
`e_s s f_s = 1`, `e_t (c_r r) f_t = 1`."**

The choice is legitimate: two-sided division applies to `d_r` and to `c_r r`
only because these are nonzero, and the two nonvanishing facts are part of the
statement rather than left implicit. -/
def PrintedCoefficientSeparationFactorizations : Prop :=
  ∀ (S : Type) [Ring S],
    (∀ z : S, z ≠ 0 → ∃ c d : S, c * z * d = 1) →
      ∀ r s : S, r ≠ 0 → s ≠ 0 →
        ∃ cr dr ed fd es fs et ft : S,
          cr * r * dr = 1 ∧ dr ≠ 0 ∧ cr * r ≠ 0 ∧
            ed * dr * fd = 1 ∧ es * s * fs = 1 ∧ et * (cr * r) * ft = 1

/-- Closed proof that the four printed factorizations can be chosen. -/
theorem manuscriptPrintedCoefficientSeparationFactorizations :
    PrintedCoefficientSeparationFactorizations := by
  intro S _ hdiv r s hr hs
  letI : Nontrivial S := ⟨⟨r, 0, hr⟩⟩
  obtain ⟨cr, dr, hcr⟩ := hdiv r hr
  have hdr : dr ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hcr
    exact zero_ne_one hcr
  have hcrr : cr * r ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hcr
    exact zero_ne_one hcr
  obtain ⟨ed, fd, hdf⟩ := hdiv dr hdr
  obtain ⟨es, fs, hsf⟩ := hdiv s hs
  obtain ⟨et, ft, htf⟩ := hdiv (cr * r) hcrr
  exact ⟨cr, dr, ed, fd, es, fs, et, ft, hcr, hdr, hcrr, hdf, hsf, htf⟩

/-- **"set `a = f_s x e_t c_r`, `b = d_r f_d y e_s`.  Then `arb = 0`.  If
`bsar = 0`, multiplication on the left by `e_d` and on the right by `f_t` gives
`yx = 0`, a contradiction."**

The printed recipe, with the four factorizations and the pair `x, y` supplied
by the caller: exactly the arithmetic the manuscript displays. -/
def PrintedCoefficientSeparationRecipe : Prop :=
  ∀ (S : Type) [Ring S] (r s cr dr ed fd es fs et ft x y : S),
    cr * r * dr = 1 → ed * dr * fd = 1 → es * s * fs = 1 →
      et * (cr * r) * ft = 1 → x * (et * fd) * y = 0 → y * x ≠ 0 →
        (fs * x * et * cr) * r * (dr * fd * y * es) = 0 ∧
          (dr * fd * y * es) * s * (fs * x * et * cr) * r ≠ 0

/-- Closed proof of the printed recipe. -/
theorem manuscriptPrintedCoefficientSeparationRecipe :
    PrintedCoefficientSeparationRecipe := by
  intro S _ r s cr dr ed fd es fs et ft x y hcr hdf hsf htf hxy hyx
  constructor
  · calc (fs * x * et * cr) * r * (dr * fd * y * es)
        = fs * x * et * (cr * r * dr) * fd * y * es := by noncomm_ring
      _ = fs * x * (et * fd) * y * es := by rw [hcr]; noncomm_ring
      _ = fs * (x * (et * fd) * y) * es := by noncomm_ring
      _ = 0 := by rw [hxy, mul_zero, zero_mul]
  · intro hzero
    apply hyx
    have hrecover :
        ed * ((dr * fd * y * es) * s * (fs * x * et * cr) * r) * ft = y * x := by
      calc ed * ((dr * fd * y * es) * s * (fs * x * et * cr) * r) * ft
          = (ed * dr * fd) * y * (es * s * fs) * x *
              (et * (cr * r) * ft) := by noncomm_ring
        _ = y * x := by rw [hdf, hsf, htf]; simp
    rw [← hrecover, hzero, mul_zero, zero_mul]

/-- **The whole printed derivation of `\eqref{eq:coefficient-separation}`.**
For nonzero `r, s` the eight factorization scalars, the pair `x, y` produced by
the preceding construction at `w = e_t f_d`, and the printed `a, b` all exist
together and satisfy `arb = 0`, `bsar ≠ 0`. -/
def PrintedCoefficientSeparation : Prop :=
  ∀ (S : Type) [Ring S] (_L : LeavittFamily S),
    (∀ z : S, z ≠ 0 → ∃ c d : S, c * z * d = 1) →
      ∀ r s : S, r ≠ 0 → s ≠ 0 →
        ∃ cr dr ed fd es fs et ft x y a b : S,
          cr * r * dr = 1 ∧ ed * dr * fd = 1 ∧ es * s * fs = 1 ∧
            et * (cr * r) * ft = 1 ∧
            x * (et * fd) * y = 0 ∧ y * x ≠ 0 ∧
            a = fs * x * et * cr ∧ b = dr * fd * y * es ∧
            a * r * b = 0 ∧ b * s * a * r ≠ 0

/-- Closed proof of the printed derivation of `\eqref{eq:coefficient-separation}`. -/
theorem manuscriptPrintedCoefficientSeparation : PrintedCoefficientSeparation := by
  intro S _ L hdiv r s hr hs
  letI : Nontrivial S := ⟨⟨r, 0, hr⟩⟩
  obtain ⟨cr, dr, ed, fd, es, fs, et, ft, hcr, _hdr, _hcrr, hdf, hsf, htf⟩ :=
    manuscriptPrintedCoefficientSeparationFactorizations S hdiv r s hr hs
  obtain ⟨x, y, hxy, hyx⟩ := exists_reversing_zero_product L hdiv (et * fd)
  obtain ⟨hab, hba⟩ :=
    manuscriptPrintedCoefficientSeparationRecipe S r s cr dr ed fd es fs et ft
      x y hcr hdf hsf htf hxy hyx
  exact ⟨cr, dr, ed, fd, es, fs, et, ft, x, y, fs * x * et * cr,
    dr * fd * y * es, hcr, hdf, hsf, htf, hxy, hyx, rfl, rfl, hab, hba⟩

/-- **`\eqref{eq:coefficient-separation}` at the manuscript's coefficient
ring.**  Two-sided division is `BinaryLeavitt.exists_mul_mul_eq_one`, so the
separation is unconditional over `L_{𝔽₂}(1,2)`. -/
def PrintedCoefficientSeparationAtBinaryLeavitt : Prop :=
  ∀ r s : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2), r ≠ 0 → s ≠ 0 →
    ∃ a b : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2),
      a * r * b = 0 ∧ b * s * a * r ≠ 0

/-- Closed proof of coefficient separation over `L_{𝔽₂}(1,2)`. -/
theorem manuscriptPrintedCoefficientSeparationAtBinaryLeavitt :
    PrintedCoefficientSeparationAtBinaryLeavitt := by
  intro r s hr hs
  exact exists_annihilate_preserve_reverse (BinaryLeavitt.family (ZMod 2))
    (fun _ hx => BinaryLeavitt.exists_mul_mul_eq_one (ZMod 2) hx) hr hs

/-! ## The diagonal branch: a conjugation that moves a root

`non_mf_groups_exist.tex`: "Suppose first that `g` is diagonal. ... If `g`
commuted with every `e_{ij}(a)`, then commuting with the `e_{ij}(1)` would
force `g = λ I_{12}`, and commuting with arbitrary `e_{ij}(a)` would make `λ` a
central unit.  Hence `g = 1`, a contradiction.  Thus for some `i ≠ j` and
`a ∈ R`, conjugation by `g` sends `e_{ij}(a)` to `e_{ij}(y)` with `y ≠ a`." -/

/-- **"Thus for some `i ≠ j` and `a ∈ R`, conjugation by `g` sends `e_{ij}(a)`
to `e_{ij}(y)` with `y ≠ a`."**

The hypotheses are exactly the ones the manuscript has in hand at this point:
the coefficient ring has no nontrivial central unit (this is what "would make
`λ` a central unit.  Hence `g = 1`" consumes), and `g` is a diagonal element of
the elementary group other than the identity.  The normal subgroup plays no
role in this sentence and is therefore absent.  The last two conjuncts are the
display that immediately follows, `[g, e_{ij}(a)] = e_{ij}(y - a)` with
`y - a ≠ 0`, written without bracket notation because the elementary group is a
subgroup and carries none. -/
def PrintedDiagonalConjugationMovesRoot : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] [Nontrivial J] (S : Type) [Ring S],
    (∀ lam : S, (∀ z : S, lam * z = z * lam) →
        (∃ mu : S, lam * mu = 1 ∧ mu * lam = 1) → lam = 1) →
      ∀ g : elementaryGroup J S, g ≠ 1 →
        (∀ u v : J, u ≠ v → elMat g u v = 0) →
          ∃ (i j : J) (hij : i ≠ j) (a y : S),
            g * elGen i j hij a * g⁻¹ = elGen i j hij y ∧ y ≠ a ∧
              g * elGen i j hij a * g⁻¹ * (elGen i j hij a)⁻¹
                = elGen i j hij (y - a) ∧ y - a ≠ 0

/-- Closed proof that a nonidentity diagonal element moves some root. -/
theorem manuscriptPrintedDiagonalConjugationMovesRoot :
    PrintedDiagonalConjugationMovesRoot := by
  intro J _ _ _ S _ hcentral g hgne hdiag
  obtain ⟨k, l, hkl⟩ := exists_pair_ne J
  by_cases hall : ∀ u v : J, u ≠ v → ∀ a : S,
      elMat g u u * (a * elMat (g⁻¹) v v) = a
  · -- Every conjugation is trivial, so `g` is a central scalar, so `g = 1`.
    exfalso
    apply hgne
    have hdiagconst : ∀ u : J, elMat g u u = elMat g k k := by
      intro u
      by_cases hu : u = k
      · rw [hu]
      · have h1 : elMat g u u * elMat (g⁻¹) k k = 1 := by
          have h2 := hall u k hu 1
          rwa [one_mul] at h2
        calc elMat g u u
            = elMat g u u * (elMat (g⁻¹) k k * elMat g k k) := by
              rw [RootDetectionBinary.elMat_inv_diag_mul g hdiag k, mul_one]
          _ = elMat g u u * elMat (g⁻¹) k k * elMat g k k := by rw [← mul_assoc]
          _ = elMat g k k := by rw [h1, one_mul]
    have hcen : ∀ z : S, elMat g k k * z = z * elMat g k k := by
      intro z
      have hx := hall k l hkl z
      calc elMat g k k * z
          = elMat g k k * (z * (elMat (g⁻¹) l l * elMat g l l)) := by
            rw [RootDetectionBinary.elMat_inv_diag_mul g hdiag l, mul_one]
        _ = elMat g k k * (z * elMat (g⁻¹) l l) * elMat g l l := by noncomm_ring
        _ = z * elMat g l l := by rw [hx]
        _ = z * elMat g k k := by rw [hdiagconst l]
    have hlam : elMat g k k = 1 :=
      hcentral (elMat g k k) hcen
        ⟨elMat (g⁻¹) k k, RootDetectionBinary.elMat_diag_mul_inv g hdiag k,
          RootDetectionBinary.elMat_inv_diag_mul g hdiag k⟩
    apply elMat_injective
    rw [elMat_one]
    ext u v
    by_cases huv : u = v
    · rw [Matrix.one_apply, if_pos huv, ← huv, hdiagconst u]
      exact hlam
    · rw [Matrix.one_apply, if_neg huv]
      exact hdiag u v huv
  · -- Some conjugation moves a root; the moved coefficient is the printed `y`.
    have hex : ∃ (u v : J) (_ : u ≠ v) (a : S),
        elMat g u u * (a * elMat (g⁻¹) v v) ≠ a := by
      by_contra hcon
      apply hall
      intro u v huv a
      by_contra ha
      exact hcon ⟨u, v, huv, a, ha⟩
    obtain ⟨u, v, huv, a, ha⟩ := hex
    have hconj : g * elGen u v huv a * g⁻¹
        = elGen u v huv (elMat g u u * (a * elMat (g⁻¹) v v)) :=
      RootDetectionBinary.conj_elGen_of_diagonal g hdiag huv a
    have hinv : (elGen u v huv a)⁻¹ = elGen (R := S) u v huv (-a) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [elGen_mul, add_neg_cancel, elGen_zero]
    refine ⟨u, v, huv, a, elMat g u u * (a * elMat (g⁻¹) v v), hconj, ha, ?_,
      sub_ne_zero_of_ne ha⟩
    rw [hconj, hinv, elGen_mul, ← sub_eq_add_neg]

/-- **The same sentence at the manuscript's coefficient ring.**  Triviality of
central units is `BinaryLeavitt.central_units_trivial`, so over `L_{𝔽₂}(1,2)`
the sentence carries no ring hypothesis at all. -/
def PrintedDiagonalConjugationMovesRootAtBinaryLeavitt : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] [Nontrivial J]
      (g : elementaryGroup J (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))),
    g ≠ 1 → (∀ u v : J, u ≠ v → elMat g u v = 0) →
      ∃ (i j : J) (hij : i ≠ j)
        (a y : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
        g * elGen i j hij a * g⁻¹ = elGen i j hij y ∧ y ≠ a

/-- Closed proof of the diagonal sentence over `L_{𝔽₂}(1,2)`. -/
theorem manuscriptPrintedDiagonalConjugationMovesRootAtBinaryLeavitt :
    PrintedDiagonalConjugationMovesRootAtBinaryLeavitt := by
  intro J _ _ _ g hgne hdiag
  obtain ⟨i, j, hij, a, y, hconj, hya, _, _⟩ :=
    manuscriptPrintedDiagonalConjugationMovesRoot J
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
      (fun lam hlam hinv => by
        obtain ⟨mu, h1, h2⟩ := hinv
        exact congrArg Units.val
          (BinaryLeavitt.central_units_trivial ⟨lam, mu, h1, h2⟩ hlam))
      g hgne hdiag
  exact ⟨i, j, hij, a, y, hconj, hya⟩

/-! ## The sparse off-diagonal branch: the surviving defect entry

`non_mf_groups_exist.tex`: "Suppose next that `g` is not diagonal, and choose
`ℓ ≠ i` with `g_{ℓi} ≠ 0`.  Put `r = (g^{-1})_{ℓi}`.  If `r = 0`, set
`A = g E_{iℓ} g^{-1}`, `B = E_{iℓ}`.  Then `AB = 0`, and the double commutator
`[g e_{iℓ}(1) g^{-1}, e_{iℓ}(1)] = 1 - BA` belongs to `N`.  Its defect `-BA` is
square-zero and supported in row `i`.  There is an `m` for which
`g_{ℓi}(g^{-1})_{ℓm} ≠ 0` ... Thus the `(i,m)` entry of the defect in
`\eqref{eq:row-unipotent-zero-inverse}` is nonzero." -/

/-- **"Thus the `(i,m)` entry of the defect in
`\eqref{eq:row-unipotent-zero-inverse}` is nonzero."**

The graded sentence is the last conjunct.  The three that precede it are what
pins down *which* object "the defect in `\eqref{eq:row-unipotent-zero-inverse}`" is:
`AB = 0`, the printed value `1 - BA` of the double commutator, and
row-support in row `i`.  Membership in `N` is a separate sentence and is
already carried by `doubleCommutator_mem`, so no normal subgroup appears here.

The hypotheses `g_{ℓi} ≠ 0` and `(g^{-1})_{ℓi} = 0` are the manuscript's own
case-split conditions, and are exactly the hypotheses of the unconditional
theorem `exists_elGen_mem_of_inv_entry_zero`. -/
def PrintedSparseDefectEntryNonzero : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (S : Type) [Ring S]
      (u : (Matrix J J S)ˣ) (i l : J) (hil : i ≠ l),
    ((u⁻¹ : (Matrix J J S)ˣ) : Matrix J J S) l i = 0 →
      (u : Matrix J J S) l i ≠ 0 →
        conjSingle u i l (1 : S) * Matrix.single i l (1 : S) = 0 ∧
          (∀ hAB : conjSingle u i l (1 : S) * Matrix.single i l (1 : S) = 0,
              ⁅u * elementaryUnit i l hil (1 : S) * u⁻¹,
                  elementaryUnit i l hil (1 : S)⁆
                = sqZeroUnit
                    (-(Matrix.single i l (1 : S) * conjSingle u i l (1 : S)))
                    (neg_mul_sq_eq_zero_of_left_annihilates
                      (conjSingle u i l (1 : S)) (Matrix.single i l (1 : S))
                      hAB)) ∧
          IsRowSupported
              (-(Matrix.single i l (1 : S) * conjSingle u i l (1 : S))) i ∧
          ∃ m : J,
            (u : Matrix J J S) l i *
                ((u⁻¹ : (Matrix J J S)ˣ) : Matrix J J S) l m ≠ 0 ∧
              (-(Matrix.single i l (1 : S) * conjSingle u i l (1 : S))) i m
                  = -((u : Matrix J J S) l i *
                    ((u⁻¹ : (Matrix J J S)ˣ) : Matrix J J S) l m) ∧
              (-(Matrix.single i l (1 : S) * conjSingle u i l (1 : S))) i m ≠ 0

/-- Closed proof that the sparse defect has a nonzero `(i,m)` entry. -/
theorem manuscriptPrintedSparseDefectEntryNonzero :
    PrintedSparseDefectEntryNonzero := by
  intro J _ _ S _ u i l hil hzero hne
  have hAB : conjSingle u i l (1 : S) * Matrix.single i l (1 : S) = 0 := by
    ext p q
    rw [matrix_mul_single_apply, Matrix.zero_apply]
    by_cases hq : q = l
    · rw [if_pos hq, conjSingle_apply, hzero, mul_zero, zero_mul]
    · rw [if_neg hq]
  refine ⟨hAB, fun h => doubleCommutator_eq_sqZeroUnit u hil hil 1 1 h,
    isRowSupported_single_mul (conjSingle u i l (1 : S)) i l 1, ?_⟩
  obtain ⟨m, hm⟩ := exists_mul_inv_entry_ne_zero u l i hne
  have hentry :
      (-(Matrix.single i l (1 : S) * conjSingle u i l (1 : S))) i m
        = -((u : Matrix J J S) l i *
            ((u⁻¹ : (Matrix J J S)ˣ) : Matrix J J S) l m) := by
    rw [Matrix.neg_apply, matrix_single_mul_apply, if_pos rfl, conjSingle_apply,
      one_mul, mul_one]
  refine ⟨m, hm, hentry, ?_⟩
  rw [hentry]
  exact neg_ne_zero.mpr hm

/-! ## The dense off-diagonal branch: the annihilating product

`non_mf_groups_exist.tex`: "It remains to treat `r ≠ 0`.  Apply
`\eqref{eq:coefficient-separation}` to `r` and `s = g_{ℓi}`, obtaining `a, b`
with `arb = 0` and `bsar ≠ 0`.  This time put `A = g(aE_{iℓ})g^{-1}`,
`B = bE_{iℓ}`.  Again `AB = 0`, because its potentially nonzero coefficient
contains `arb`." -/

/-- **"Again `AB = 0`, because its potentially nonzero coefficient contains
`arb`."**

The first conjunct *is* the printed reason: every entry of `AB` is either `0`
or `g_{pi}` times the coefficient `a r b`, with `r = (g^{-1})_{ℓi}`.  The
second is the conclusion the sentence draws from it.  The hypothesis
`a r b = 0` is the first half of `\eqref{eq:coefficient-separation}`, produced
unconditionally over `L_{𝔽₂}(1,2)` by
`manuscriptPrintedCoefficientSeparationAtBinaryLeavitt`. -/
def PrintedDenseAnnihilatingProduct : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (S : Type) [Ring S]
      (u : (Matrix J J S)ˣ) (i l : J) (a b : S),
    a * ((u⁻¹ : (Matrix J J S)ˣ) : Matrix J J S) l i * b = 0 →
      (∀ p q : J,
          (conjSingle u i l a * Matrix.single i l b) p q
            = if q = l then
                (u : Matrix J J S) p i *
                  (a * ((u⁻¹ : (Matrix J J S)ˣ) : Matrix J J S) l i * b)
              else 0) ∧
        conjSingle u i l a * Matrix.single i l b = 0

/-- Closed proof that the dense product vanishes, with the printed reason. -/
theorem manuscriptPrintedDenseAnnihilatingProduct :
    PrintedDenseAnnihilatingProduct := by
  intro J _ _ S _ u i l a b hzero
  have hentry : ∀ p q : J,
      (conjSingle u i l a * Matrix.single i l b) p q
        = if q = l then
            (u : Matrix J J S) p i *
              (a * ((u⁻¹ : (Matrix J J S)ˣ) : Matrix J J S) l i * b)
          else 0 := by
    intro p q
    rw [matrix_mul_single_apply]
    by_cases hq : q = l
    · rw [if_pos hq, if_pos hq, conjSingle_apply]
      simp only [mul_assoc]
    · rw [if_neg hq, if_neg hq]
  refine ⟨hentry, ?_⟩
  ext p q
  rw [hentry p q, Matrix.zero_apply]
  by_cases hq : q = l
  · rw [if_pos hq, hzero, mul_zero]
  · rw [if_neg hq]

/-! ## The five sentences together -/

/-- The five printed coefficient calculations of `prop:simple` that the tree
previously proved only inside larger proofs, as one closed proposition. -/
def PrintedLeavittCoefficientCalculations : Prop :=
  PrintedReversedProductVanishingImplication ∧
    PrintedCoefficientSeparationFactorizations ∧
    PrintedDiagonalConjugationMovesRoot ∧
    PrintedSparseDefectEntryNonzero ∧
    PrintedDenseAnnihilatingProduct

/-- Closed proof of all five printed calculations. -/
theorem manuscriptPrintedLeavittCoefficientCalculations :
    PrintedLeavittCoefficientCalculations :=
  ⟨manuscriptPrintedReversedProductVanishingImplication,
    manuscriptPrintedCoefficientSeparationFactorizations,
    manuscriptPrintedDiagonalConjugationMovesRoot,
    manuscriptPrintedSparseDefectEntryNonzero,
    manuscriptPrintedDenseAnnihilatingProduct⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
