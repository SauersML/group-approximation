import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAffineWordProblem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ElementaryGroupFacts

/-!
# The word problem of `G_Δ`: tables and their values

`simple_kazhdan_sofic_group.tex` at 8b36733d7, section "LEF groups", l.447–451:

> A word in the generators of $G_\Delta$ multiplies out to a matrix with entries
> $\sum_\xi p_\xi u_\xi$, where each $p_\xi$ is a polynomial over $\F_2$ in finitely many
> coordinates $x(\delta)$, as $u_\xi e_Uu_\xi^{-1}$ is the indicator of
> $\{x:x(\delta)=1+c(\delta)\}$ for $\xi\colon x\mapsto\delta x+c$.

`G_Δ = EL_3(R_Δ)` with `R_Δ = LC(Ω, F_2) ⋊ Λ`. For generators `t : ι → Δ` the letters `lampGen t`
generate `Λ` (the normal form of `Λ` is skf-consequences' `LamplighterAffineWordProblem`), and a word
`p` in these letters stands for an element `ξ_p` of `Λ`.

* A monomial `(F, w)` stands for `(∏_{p ∈ F} u_p e_U u_p⁻¹) u_w`, where `u_p e_U u_p⁻¹ = e_U ∘ ξ_p⁻¹`
  is `factorFn t p` (`monoEval`). An entry is a list of monomials, standing for their sum
  (`entryEval`), and a matrix is a `3 × 3` array of entries (`matEval`).
* `monoEval_monoMul`: `(F, w)(F', w') = (F ++ wF', ww')` by covariance, so `matMul` multiplies out
  products (`matEval_matMul`).
* `gens t`: the generators `e_ij(s)` of `G_Δ` with `s ∈ {e_U, 1} ∪ {u_ξ^{±1} : ξ a letter of Λ}`;
  `closure_range_gens`: they generate `G_Δ`.
* `coe_wordValue_gens`: a word in them multiplies out to `matEval t (wordMat w)`, and
  `wordValue_gens_eq_one_iff` with `matEval_eq_one_iff`: it is trivial exactly when every entry of
  its difference from `I_3` vanishes.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Lamplighter
namespace Host

open Multiplicative

/-! ## Tables -/

/-- A monomial `(F, w)`: the prefixes `F` and the unit word `w`, words in the letters of `Λ`. -/
abbrev Mono (ι : Type*) : Type _ :=
  List (List (Option ι × Bool)) × List (Option ι × Bool)

/-- An entry: a list of monomials, standing for their sum. -/
abbrev Entry (ι : Type*) : Type _ :=
  List (Mono ι)

/-- A `3 × 3` matrix of entries. -/
abbrev Mat (ι : Type*) : Type _ :=
  Fin 3 → Fin 3 → Entry ι

/-- The letters of `R_Δ`: `none ↦ e_U`, `some none ↦ 1` and `some (some x) ↦ u_x^{±1}`. -/
abbrev Letter (ι : Type*) : Type _ :=
  Option (Option (Option ι × Bool))

/-- The generators `(i, j, s)` of `G_Δ`, standing for `e_ij(s)`, and for `1` when `i = j`. -/
abbrev Gen (ι : Type*) : Type _ :=
  Fin 3 × Fin 3 × Letter ι

variable {ι : Type*}

/-- The product of monomials: `(F, w)(F', w') = (F ++ wF', ww')`. -/
def monoMul (m m' : Mono ι) : Mono ι :=
  (m.1 ++ m'.1.map (m.2 ++ ·), m.2 ++ m'.2)

/-- The product of entries. -/
def entryMul (e f : Entry ι) : Entry ι :=
  e.flatMap fun m => f.map (monoMul m)

/-- The product of matrices. -/
def matMul (A B : Mat ι) (i j : Fin 3) : Entry ι :=
  entryMul (A i 0) (B 0 j) ++ entryMul (A i 1) (B 1 j) ++ entryMul (A i 2) (B 2 j)

/-- The entry `1`. -/
def oneEntry : Entry ι :=
  [([], [])]

/-- The identity matrix. -/
def matOne (i j : Fin 3) : Entry ι :=
  if i = j then oneEntry else []

/-- The entry of a letter. -/
def letterEntry : Letter ι → Entry ι
  | none => [([[]], [])]
  | some none => oneEntry
  | some (some x) => [([], [x])]

/-- The matrix `I + E_ij(s)` of a generator `(i, j, s)`; it is `I` when `i = j`. -/
def genMat (g : Gen ι) (p q : Fin 3) : Entry ι :=
  if p = q then oneEntry else if p = g.1 ∧ q = g.2.1 then letterEntry g.2.2 else []

/-- A word multiplied out. The signs are dropped, as `e_ij(s)⁻¹ = e_ij(s)` in characteristic `2`. -/
def wordMat (w : List (Gen ι × Bool)) : Mat ι :=
  w.foldr (fun x A => matMul (genMat x.1) A) matOne

theorem wordMat_nil : wordMat ([] : List (Gen ι × Bool)) = matOne :=
  rfl

theorem wordMat_cons (x : Gen ι × Bool) (w : List (Gen ι × Bool)) :
    wordMat (x :: w) = matMul (genMat x.1) (wordMat w) :=
  rfl

/-- The entries of `A - I = A + I`. -/
def diffEntry (A : Mat ι) (i j : Fin 3) : Entry ι :=
  if i = j then A i j ++ oneEntry else A i j

/-! ## Values -/

variable {Δ : Type} [Group Δ] (t : ι → Δ)

/-- `u_p e_U u_p⁻¹ = e_U ∘ ξ_p⁻¹`, for a word `p` in the letters of `Λ`. -/
noncomputable def factorFn (p : List (Option ι × Bool)) :
    LocallyConstant (LampSpace Δ) (ZMod 2) :=
  LocallyConstant.comap
    (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) (wordValue (lampGen t) p)⁻¹)
    (coord Δ 1)

/-- The value `(∏_{p ∈ F} e_U ∘ ξ_p⁻¹) u_w` of a monomial `(F, w)`. -/
noncomputable def monoEval (m : Mono ι) : LampRing Δ :=
  ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)
      (m.1.map (factorFn t)).prod *
    (ClopenGroupCrossedProduct.unit (LampAffine Δ) (LampSpace Δ) (ZMod 2)
      (wordValue (lampGen t) m.2) : LampRing Δ)

/-- The value of an entry: the sum of its monomials. -/
noncomputable def entryEval (e : Entry ι) : LampRing Δ :=
  (e.map (monoEval t)).sum

/-- The value of a matrix. -/
noncomputable def matEval (A : Mat ι) : Matrix (Fin 3) (Fin 3) (LampRing Δ) :=
  Matrix.of fun i j => entryEval t (A i j)

/-- Conjugating a factor by `u_w` prefixes `w`. -/
theorem comap_factorFn (u p : List (Option ι × Bool)) :
    LocallyConstant.comap
        (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) (wordValue (lampGen t) u)⁻¹)
        (factorFn t p) =
      factorFn t (u ++ p) := by
  ext x
  simp only [factorFn, LocallyConstant.coe_comap_apply, ClopenGroupCoeff.smulMap_apply,
    wordValue_append, mul_inv_rev, mul_smul]

theorem comap_prod_factorFn (u : List (Option ι × Bool)) (F : List (List (Option ι × Bool))) :
    LocallyConstant.comap
        (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) (wordValue (lampGen t) u)⁻¹)
        (F.map (factorFn t)).prod =
      ((F.map (u ++ ·)).map (factorFn t)).prod := by
  induction F with
  | nil => rfl
  | cons p F ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← ih, ← comap_factorFn]
    rfl

/-- **Multiplying monomials** (tex l.450): `(F, w)(F', w') = (F ++ wF', ww')`, by covariance. -/
theorem monoEval_monoMul (m m' : Mono ι) :
    monoEval t (monoMul m m') = monoEval t m * monoEval t m' := by
  simp only [monoEval]
  rw [ClopenGroupCrossedProduct.coeff_mul_unit_mul_coeff_mul_unit, comap_prod_factorFn]
  simp only [monoMul, List.map_append, List.prod_append, wordValue_append]

theorem entryEval_nil : entryEval t ([] : Entry ι) = 0 :=
  rfl

theorem entryEval_cons (m : Mono ι) (e : Entry ι) :
    entryEval t (m :: e) = monoEval t m + entryEval t e := by
  simp only [entryEval, List.map_cons, List.sum_cons]

theorem entryEval_append (e f : Entry ι) :
    entryEval t (e ++ f) = entryEval t e + entryEval t f := by
  simp only [entryEval, List.map_append, List.sum_append]

theorem entryEval_map_monoMul (m : Mono ι) (f : Entry ι) :
    entryEval t (f.map (monoMul m)) = monoEval t m * entryEval t f := by
  simp only [entryEval, List.map_map, Function.comp_def, monoEval_monoMul, List.sum_map_mul_left]

theorem entryEval_entryMul (e f : Entry ι) :
    entryEval t (entryMul e f) = entryEval t e * entryEval t f := by
  induction e with
  | nil =>
    show (0 : LampRing Δ) = 0 * entryEval t f
    rw [zero_mul]
  | cons m e ih =>
    have h : entryMul (m :: e) f = f.map (monoMul m) ++ entryMul e f := by
      simp only [entryMul, List.flatMap_cons]
    rw [h, entryEval_append, entryEval_map_monoMul, ih, entryEval_cons, add_mul]

theorem matEval_matMul (A B : Mat ι) : matEval t (matMul A B) = matEval t A * matEval t B := by
  ext i j
  simp only [matEval, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three, matMul,
    entryEval_append, entryEval_entryMul]

theorem entryEval_oneEntry : entryEval t (oneEntry : Entry ι) = 1 := by
  simp only [oneEntry, entryEval, monoEval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, List.prod_nil, map_one, one_mul, wordValue_nil]
  rw [ClopenGroupCrossedProduct.val_unit, SkewMonoidAlgebra.single_one_one]

theorem matEval_matOne : matEval t (matOne : Mat ι) = 1 := by
  ext i j
  rw [matEval, Matrix.of_apply, matOne, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, entryEval_oneEntry]
  · rw [if_neg h, if_neg h]
    rfl

/-! ## Characteristic two -/

theorem one_add_one_lampRing : (1 : LampRing Δ) + 1 = 0 := by
  have h : (1 + 1 : LocallyConstant (LampSpace Δ) (ZMod 2)) = 0 :=
    LocallyConstant.ext fun _ => by
      show (1 : ZMod 2) + 1 = 0
      decide
  rw [← map_one (ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)),
    ← map_add, h, map_zero]

theorem add_self_lampRing (r : LampRing Δ) : r + r = 0 := by
  rw [← one_mul r, ← add_mul, one_add_one_lampRing, zero_mul]

/-- **A matrix is `I_3`** exactly when every entry of its difference from `I_3` vanishes. -/
theorem matEval_eq_one_iff (A : Mat ι) :
    matEval t A = 1 ↔ ∀ i j, entryEval t (diffEntry A i j) = 0 := by
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [matEval, Matrix.of_apply, Matrix.one_apply] at hij
    unfold diffEntry
    by_cases hh : i = j
    · rw [if_pos hh] at hij ⊢
      rw [entryEval_append, entryEval_oneEntry, hij, one_add_one_lampRing]
    · rw [if_neg hh] at hij ⊢
      exact hij
  · intro h
    refine Matrix.ext fun i j => ?_
    have hij := h i j
    rw [matEval, Matrix.of_apply, Matrix.one_apply]
    unfold diffEntry at hij
    by_cases hh : i = j
    · rw [if_pos hh] at hij ⊢
      rw [entryEval_append, entryEval_oneEntry] at hij
      calc entryEval t (A i j) = entryEval t (A i j) + 1 + 1 := by
            rw [add_assoc, one_add_one_lampRing, add_zero]
        _ = 1 := by rw [hij, zero_add]
    · rw [if_neg hh] at hij ⊢
      exact hij

/-! ## The generators -/

/-- **The generators of `G_Δ`**: `e_ij(s)` for `i ≠ j` and a letter `s`, and `1` for `i = j`. -/
noncomputable def gens (g : Gen ι) : ↥(elementaryGroup (Fin 3) (LampRing Δ)) :=
  if h : g.1 = g.2.1 then 1
  else ⟨elementaryUnit g.1 g.2.1 h (entryEval t (letterEntry g.2.2)), elementaryUnit_mem _ _ h _⟩

/-- `e_ij(s)⁻¹ = e_ij(-s) = e_ij(s)`. -/
theorem gens_inv (g : Gen ι) : (gens t g)⁻¹ = gens t g := by
  refine inv_eq_of_mul_eq_one_right ?_
  unfold gens
  split_ifs with h
  · exact mul_one 1
  · refine Subtype.ext ?_
    show elementaryUnit g.1 g.2.1 h (entryEval t (letterEntry g.2.2)) *
      elementaryUnit g.1 g.2.1 h (entryEval t (letterEntry g.2.2)) = 1
    rw [elementaryUnit_mul, add_self_lampRing, elementaryUnit_zero]

theorem matEval_genMat (g : Gen ι) :
    matEval t (genMat g) =
      (((gens t g : ↥(elementaryGroup (Fin 3) (LampRing Δ))) :
        (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) : Matrix (Fin 3) (Fin 3) (LampRing Δ)) := by
  obtain ⟨i, j, s⟩ := g
  refine Matrix.ext fun p q => ?_
  rw [matEval, Matrix.of_apply]
  dsimp only [genMat, gens]
  by_cases h : i = j
  · rw [dif_pos h]
    show _ = (1 : Matrix (Fin 3) (Fin 3) (LampRing Δ)) p q
    rw [Matrix.one_apply]
    by_cases hpq : p = q
    · rw [if_pos hpq, if_pos hpq, entryEval_oneEntry]
    · rw [if_neg hpq, if_neg hpq, if_neg fun e => hpq (e.1.trans (h.trans e.2.symm))]
      rfl
  · rw [dif_neg h]
    show _ = (1 + Matrix.single i j (entryEval t (letterEntry s)) :
      Matrix (Fin 3) (Fin 3) (LampRing Δ)) p q
    rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    by_cases hpq : p = q
    · rw [if_pos hpq, if_pos hpq, entryEval_oneEntry,
        if_neg fun e : i = p ∧ j = q => h (e.1.trans (hpq.trans e.2.symm)), add_zero]
    · rw [if_neg hpq, if_neg hpq, zero_add]
      by_cases hij : p = i ∧ q = j
      · rw [if_pos hij, if_pos (⟨hij.1.symm, hij.2.symm⟩ : i = p ∧ j = q)]
      · rw [if_neg hij, if_neg fun e : i = p ∧ j = q => hij ⟨e.1.symm, e.2.symm⟩]
        rfl

/-- **Multiplying out** (tex l.447–448): a word in the generators is `matEval t (wordMat w)`. -/
theorem coe_wordValue_gens (w : List (Gen ι × Bool)) :
    (((wordValue (gens t) w : ↥(elementaryGroup (Fin 3) (LampRing Δ))) :
        (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) : Matrix (Fin 3) (Fin 3) (LampRing Δ)) =
      matEval t (wordMat w) := by
  induction w with
  | nil =>
    rw [wordValue_nil, wordMat_nil, matEval_matOne]
    rfl
  | cons x w ih =>
    obtain ⟨g, b⟩ := x
    have hg : (if b then gens t g else (gens t g)⁻¹) = gens t g := by
      cases b
      · exact gens_inv t g
      · rfl
    rw [wordValue_cons]
    dsimp only
    rw [hg, Subgroup.coe_mul, Units.val_mul, ih]
    show _ = matEval t (matMul (genMat g) (wordMat w))
    rw [matEval_matMul, matEval_genMat]

theorem wordValue_gens_eq_one_iff (w : List (Gen ι × Bool)) :
    wordValue (gens t) w = 1 ↔ matEval t (wordMat w) = 1 := by
  rw [← coe_wordValue_gens, Units.val_eq_one, OneMemClass.coe_eq_one]

/-! ## Generation -/

theorem closure_range_lampGen {t : ι → Δ} (ht : Subgroup.closure (Set.range t) = ⊤) :
    Subgroup.closure (Set.range (lampGen t)) = ⊤ := by
  refine eq_top_iff.2 ((closure_insert_lampAdd_image_inr Δ ht).symm.le.trans
    (Subgroup.closure_mono ?_))
  rintro _ (rfl | ⟨_, ⟨i, rfl⟩, rfl⟩)
  · exact ⟨none, rfl⟩
  · exact ⟨some i, rfl⟩

theorem entryEval_letterEntry_unit (o : Option ι) (b : Bool) :
    entryEval t (letterEntry (some (some (o, b)))) =
      (ClopenGroupCrossedProduct.unit (LampAffine Δ) (LampSpace Δ) (ZMod 2)
        (if b then lampGen t o else (lampGen t o)⁻¹) : LampRing Δ) := by
  show entryEval t [(([] : List (List (Option ι × Bool))), [(o, b)])] = _
  simp only [entryEval, monoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, List.prod_nil, map_one, one_mul, wordValue_cons, wordValue_nil, mul_one]

theorem entryEval_letterEntry_none :
    entryEval t (letterEntry (none : Letter ι)) =
      ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)
        (LocallyConstant.charFn (ZMod 2) (isClopen_coordOne Δ)) := by
  have hf : factorFn t ([] : List (Option ι × Bool)) = coord Δ 1 := by
    ext x
    rw [factorFn, LocallyConstant.coe_comap_apply, ClopenGroupCoeff.smulMap_apply, wordValue_nil,
      inv_one, one_smul]
  show entryEval t [(([[]] : List (List (Option ι × Bool))), ([] : List (Option ι × Bool)))] = _
  simp only [entryEval, monoEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, List.prod_cons, List.prod_nil, mul_one, hf, wordValue_nil, charFn_coordOne]
  rw [ClopenGroupCrossedProduct.val_unit, SkewMonoidAlgebra.single_one_one, mul_one]

/-- Every printed generator of `R_Δ`, and `1`, is the value of a letter. -/
theorem exists_letterEntry {s : LampRing Δ}
    (hs : s ∈ insert 1 (lampRingGenerators Δ (Set.range (lampGen t)))) :
    ∃ ℓ : Letter ι, entryEval t (letterEntry ℓ) = s := by
  rcases hs with rfl | rfl | (⟨_, ⟨o, rfl⟩, rfl⟩ | ⟨_, ⟨o, rfl⟩, rfl⟩) | rfl
  · exact ⟨some none, entryEval_oneEntry t⟩
  · exact ⟨some none, entryEval_oneEntry t⟩
  · refine ⟨some (some (o, true)), ?_⟩
    rw [entryEval_letterEntry_unit]
    rfl
  · refine ⟨some (some (o, false)), ?_⟩
    rw [entryEval_letterEntry_unit]
    exact congrArg Units.val (ClopenGroupCrossedProduct.unit_inv (LampAffine Δ) (LampSpace Δ)
      (ZMod 2) (lampGen t o)).symm
  · exact ⟨none, entryEval_letterEntry_none t⟩

/-- **The generators generate `G_Δ`** (tex l.365–368 and eq:elementary). -/
theorem closure_range_gens {t : ι → Δ} (ht : Subgroup.closure (Set.range t) = ⊤) :
    Subgroup.closure (Set.range (gens t)) = ⊤ := by
  have hgen := printedElementaryGeneration (LampRing Δ)
    (lampRingGenerators Δ (Set.range (lampGen t)))
    (closure_generators_eq_top Δ (closure_range_lampGen ht))
  have hle : elementaryGroup (Fin 3) (LampRing Δ) ≤
      (Subgroup.closure (Set.range (gens t))).map
        (elementaryGroup (Fin 3) (LampRing Δ)).subtype := by
    refine hgen.le.trans ?_
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨i, j, h, s, hs, rfl⟩
    obtain ⟨ℓ, hℓ⟩ := exists_letterEntry t hs
    refine ⟨gens t (i, j, ℓ), ⟨(i, j, ℓ), rfl⟩, ?_⟩
    show ((gens t (i, j, ℓ) : ↥(elementaryGroup (Fin 3) (LampRing Δ))) :
      (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) = elementaryUnit i j h s
    simp only [gens, dif_neg h]
    rw [hℓ]
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨g', hg', he⟩ := Subgroup.mem_map.1 (hle g.2)
  rwa [show g' = g from Subtype.ext he] at hg'

end Host
end Lamplighter
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.Host.monoEval_monoMul
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.Host.coe_wordValue_gens
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.Host.matEval_eq_one_iff
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.Host.closure_range_gens
