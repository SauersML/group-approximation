import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.SiteRep
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.MatWordReduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.FGMain
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordTablePrimrec
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(X)` computes the word problem of the derived topological full group

SK row `e5932a45f053` (tex l.724–726, Grigorchuk–Medynets, Thm 1.1(3)), the direction "if `L(X)`
is recursive then the word problem is solvable", as a Turing reduction.

The finite generating family `genFam` of `D = ⁅[[σ]], [[σ]]⁆` enumerates `gens S N`
(`derivedFullGroupSubshift_eq_closure_gens`). Each generator is a tower permutation over a cylinder
on `[0, N]`, or `1`, and it is represented in `LC(X, F₂) ⋊ ℤ` by an explicit table
(`siteRep_genTab`). A word `w` goes to the diagonal matrix of tables `diag(t_w, 1, 1)`, where `t_w`
is the product of the letter tables. It evaluates to `1` iff the word is trivial
(`SiteRep.eq_one_iff`), and `turingReducible_of_matWord` gives the reduction.
-/

namespace GroupApproximation.Full.SKTFG

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.CylinderTables
open GroupApproximation.Full.StepanovMatui.Matui
open SymbolicDynamics.FullShift

variable {A : Type}

section Diag

/-- The diagonal matrix `diag(t, 1, 1)` of tables. -/
def diagMat (t : Table A) (p q : Fin 3) : Table A :=
  if p = q then (if p = 0 then t else [((0 : ℤ), ([] : Cyl A))]) else []

/-- A word multiplied out as a product of diagonal matrices of tables. -/
def wordDiag {ι : Type*} (tab : ι × Bool → Table A) (w : List (ι × Bool)) : Mat A :=
  (w.map fun ℓ => diagMat (tab ℓ)).foldr matMul matOne

theorem primrec_wordDiag [Primcodable A] {ι : Type*} [Primcodable ι] [Finite ι]
    (tab : ι × Bool → Table A) : Primrec (wordDiag tab) :=
  (Primrec.list_foldr (Primrec.list_map Primrec.id
      ((Primrec.dom_finite fun ℓ : ι × Bool => (diagMat (tab ℓ) : Mat A)).comp Primrec.snd).to₂)
    (Primrec.const (matOne : Mat A))
    (primrec_matMul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun _ => rfl

theorem coe_wordValue {G : Type*} [Group G] {H : Subgroup G} {ι : Type*} (s : ι → H)
    (w : List (ι × Bool)) : ((wordValue s w : H) : G) = wordValue (fun i => (s i : G)) w := by
  induction w with
  | nil => rfl
  | cons ℓ w ih =>
    obtain ⟨i, b⟩ := ℓ
    show (((if b then s i else (s i)⁻¹) * wordValue s w : H) : G) =
      (if b then (s i : G) else (s i : G)⁻¹) * wordValue (fun i => (s i : G)) w
    rw [Subgroup.coe_mul, ih]
    cases b <;> rfl

end Diag

variable [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A] (S : Subshift A ℤ)

omit [DecidableEq A] in
theorem matEval_diagMat (t : Table A) :
    matEval (SimpleKazhdanSofic.subshiftHomeo S) (diagMat t) =
      Matrix.diagonal fun p => if p = 0 then eval (SimpleKazhdanSofic.subshiftHomeo S) t else 1 := by
  refine Matrix.ext fun p q => ?_
  rw [matEval_apply, diagMat, Matrix.diagonal_apply]
  by_cases hpq : p = q
  · by_cases hp : p = 0
    · simp only [if_pos hpq, if_pos hp]
    · simp only [if_pos hpq, if_neg hp, eval_unitTable]
  · simp only [if_neg hpq, eval_nil]

/-- The product of the letter tables of a word. -/
noncomputable def wordTable {ι : Type*} (tab : ι × Bool → Table A) (w : List (ι × Bool)) :
    ClopenCrossedProduct (SimpleKazhdanSofic.subshiftHomeo S) (ZMod 2) :=
  (w.map fun ℓ => eval (SimpleKazhdanSofic.subshiftHomeo S) (tab ℓ)).prod

theorem matEval_wordDiag {ι : Type*} (tab : ι × Bool → Table A) (w : List (ι × Bool)) :
    matEval (SimpleKazhdanSofic.subshiftHomeo S) (wordDiag tab w) =
      Matrix.diagonal fun p => if p = 0 then wordTable S tab w else 1 := by
  induction w with
  | nil =>
    rw [wordDiag, List.map_nil, List.foldr_nil, matEval_matOne]
    simp only [wordTable, List.map_nil, List.prod_nil, ite_self, Matrix.diagonal_one]
  | cons ℓ w ih =>
    have e : wordDiag tab (ℓ :: w) = matMul (diagMat (tab ℓ)) (wordDiag tab w) := rfl
    have e' : wordTable S tab (ℓ :: w) =
        eval (SimpleKazhdanSofic.subshiftHomeo S) (tab ℓ) * wordTable S tab w := by
      rw [wordTable, List.map_cons, List.prod_cons]
      rfl
    rw [e, matEval_matMul _ (fun _ => rfl), ih, matEval_diagMat, Matrix.diagonal_mul_diagonal, e']
    congr 1
    funext p
    by_cases hp : p = 0
    · simp only [if_pos hp]
    · simp only [if_neg hp, mul_one]

theorem matEval_wordDiag_eq_one_iff {ι : Type*} (tab : ι × Bool → Table A)
    (w : List (ι × Bool)) :
    matEval (SimpleKazhdanSofic.subshiftHomeo S) (wordDiag tab w) = 1 ↔ wordTable S tab w = 1 := by
  rw [matEval_wordDiag]
  constructor
  · intro h
    simpa using congrFun (congrFun h 0) 0
  · intro h
    rw [h]
    simp only [ite_self, Matrix.diagonal_one]

omit [DecidableEq A] in
/-- A word in permutations is represented by the product of its letter tables. -/
theorem siteRep_wordTable {ι : Type*} (tab : ι × Bool → Table A) (g : ι → Equiv.Perm S.carrier)
    (hg : ∀ ℓ : ι × Bool, SiteRep (SimpleKazhdanSofic.subshiftHomeo S)
      (eval (SimpleKazhdanSofic.subshiftHomeo S) (tab ℓ)) (if ℓ.2 then g ℓ.1 else (g ℓ.1)⁻¹))
    (w : List (ι × Bool)) :
    SiteRep (SimpleKazhdanSofic.subshiftHomeo S) (wordTable S tab w) (wordValue g w) := by
  induction w with
  | nil => exact SiteRep.one _
  | cons ℓ w ih =>
    obtain ⟨i, b⟩ := ℓ
    exact (hg (i, b)).mul _ ih

/-! ## The generators and their tables -/

/-- The cylinder of a word `w` on `[0, N]`, as a list of constraints. -/
noncomputable def cylList (N : ℕ) (w : Finset.Icc (0 : ℤ) N → A) : Cyl A :=
  (Finset.univ : Finset (Finset.Icc (0 : ℤ) N)).toList.map fun n => ((n : ℤ), w n)

omit [DiscreteTopology A] [DecidableEq A] in
theorem mem_cylW_iff (N : ℕ) (w : Finset.Icc (0 : ℤ) N → A) (y : S.carrier) :
    y ∈ cylW S N w ↔ cylMem (cylList N w) y.1 := by
  rw [cylW, Set.mem_iInter]
  constructor
  · intro h q hq
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hq
    exact h n
  · intro h n
    exact h _ (List.mem_map.2 ⟨n, Finset.mem_toList.2 (Finset.mem_univ n), rfl⟩)

open Classical in
/-- The table of the signed generator `(p, b)`: the tower table of `σ^{±1}` over the cylinder of
`w`, where `p = (w, σ)`, or the table of `1`. -/
noncomputable def genTab (N : ℕ) (p : (Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5))
    (b : Bool) : Table A :=
  if TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cylW S N p.1) 4 then
    towerTable (cylList N p.1)
      (if b then (p.2 : Equiv.Perm (Fin 5)) else (p.2 : Equiv.Perm (Fin 5))⁻¹)
  else [((0 : ℤ), ([] : Cyl A))]

open Classical in
theorem siteRep_genTab (N : ℕ) (p : (Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5))
    (b : Bool) :
    SiteRep (SimpleKazhdanSofic.subshiftHomeo S)
      (eval (SimpleKazhdanSofic.subshiftHomeo S) (genTab S N p b))
      (if b then genPerm S N p else (genPerm S N p)⁻¹) := by
  rw [genTab, genPerm]
  by_cases h : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cylW S N p.1) 4
  · rw [if_pos h, dif_pos h]
    cases b
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
        ← map_inv (towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cylW S N p.1)
          (towerLevels 4) h)]
      exact siteRep_towerTable S (mem_cylW_iff S N p.1) h _
    · rw [if_pos (rfl : true = true), if_pos (rfl : true = true)]
      exact siteRep_towerTable S (mem_cylW_iff S N p.1) h _
  · rw [if_neg h, dif_neg h]
    cases b
    · rw [if_neg Bool.false_ne_true, inv_one]
      exact siteRep_unitTable S
    · rw [if_pos (rfl : true = true)]
      exact siteRep_unitTable S

/-- The generators `gens S N`, enumerated by `e`, as elements of `D = [[σ]]'`. -/
noncomputable def genFam {N k : ℕ}
    (hDG : derivedFullGroupSubshift S = Subgroup.closure (gens S N))
    (e : ((Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5)) ≃ Fin k) :
    Fin k → ↥(derivedFullGroupSubshift S) := fun i =>
  ⟨genPerm S N (e.symm i), by
    rw [hDG]
    exact Subgroup.subset_closure ⟨_, rfl⟩⟩

omit [DiscreteTopology A] [DecidableEq A] in
theorem closure_range_genFam {N k : ℕ}
    (hDG : derivedFullGroupSubshift S = Subgroup.closure (gens S N))
    (e : ((Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5)) ≃ Fin k) :
    Subgroup.closure (Set.range (genFam S hDG e)) = ⊤ := by
  have hrange : (derivedFullGroupSubshift S).subtype '' Set.range (genFam S hDG e) = gens S N := by
    ext g
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨e.symm i, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨genFam S hDG e (e p), ⟨e p, rfl⟩, by
        show genPerm S N (e.symm (e p)) = genPerm S N p
        rw [Equiv.symm_apply_apply]⟩
  have hmap : (Subgroup.closure (Set.range (genFam S hDG e))).map
      (derivedFullGroupSubshift S).subtype = derivedFullGroupSubshift S := by
    rw [MonoidHom.map_closure, hrange, ← hDG]
  apply Subgroup.map_injective (derivedFullGroupSubshift S).subtype_injective
  rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem wordValue_genFam_eq_one_iff [Finite A] (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) {N k : ℕ}
    (hDG : derivedFullGroupSubshift S = Subgroup.closure (gens S N))
    (e : ((Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5)) ≃ Fin k)
    (w : List (Fin k × Bool)) :
    wordValue (genFam S hDG e) w = 1 ↔
      matEval (SimpleKazhdanSofic.subshiftHomeo S)
        (wordDiag (fun ℓ => genTab S N (e.symm ℓ.1) ℓ.2) w) = 1 := by
  have h1 : wordValue (genFam S hDG e) w = 1 ↔
      ((wordValue (genFam S hDG e) w : ↥(derivedFullGroupSubshift S)) :
        Equiv.Perm S.carrier) = 1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [h1, coe_wordValue, matEval_wordDiag_eq_one_iff]
  exact (SiteRep.eq_one_iff _
    (fun j hj y => SK05.subshiftHomeo_zpow_apply_ne_self S hinf hmin hj y)
    (siteRep_wordTable S (fun ℓ => genTab S N (e.symm ℓ.1) ℓ.2)
      (fun i => (genFam S hDG e i : Equiv.Perm S.carrier))
      (fun ℓ => siteRep_genTab S N (e.symm ℓ.1) ℓ.2) w)).symm

open Classical in
/-- **`L(X)` computes the word problem of `[[σ]]'`** in the generators `genFam`. -/
theorem turingReducible_wordProblem_genFam [Fintype A] [Primcodable A]
    (hinf : Infinite S.carrier) (hmin : SimpleKazhdanSofic.IsMinimal S) {N k : ℕ}
    (hDG : derivedFullGroupSubshift S = Subgroup.closure (gens S N))
    (e : ((Finset.Icc (0 : ℤ) N → A) × alternatingGroup (Fin 5)) ≃ Fin k) :
    TuringReducible (wordProblemOracle (genFam S hDG e)) (languageOracle S) := by
  have hlang : ∀ v : List A, v ∈ language S ↔ v ∈ listLanguage S.carrier :=
    fun v => mem_listLanguage_iff.symm
  refine turingReducible_of_matWord S.mapsTo (SimpleKazhdanSofic.subshiftHomeo S)
    (primrec_wordDiag fun ℓ : Fin k × Bool => genTab S N (e.symm ℓ.1) ℓ.2)
    (fun w => wordValue (genFam S hDG e) w = 1)
    (wordValue_genFam_eq_one_iff S hinf hmin hDG e) (fun n => rfl) fun n => ?_
  show Part.some (if ∃ v : List A, Encodable.decode n = some v ∧ v ∈ language S then 1 else 0) = _
  simp only [hlang]

end GroupApproximation.Full.SKTFG

#audit_axioms GroupApproximation.Full.SKTFG.closure_range_genFam
#audit_axioms GroupApproximation.Full.SKTFG.turingReducible_wordProblem_genFam
