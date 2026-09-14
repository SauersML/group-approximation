import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordOracle
import GroupApproximation.Dynamics.ClopenCrossedProductComap
import GroupApproximation.Meta.AxiomGuard

/-!
# The language reduces to the word problem

Section "Word problems" of `simple_kazhdan_sofic_group.tex` (origin tip e80dcf20a), proof, first
paragraph:

> Conversely, by (eq:elementary) a word for `e_12(∏_{t<n} u^{-t} e_{v_t} u^t)` is computable from
> `v = v_0 ⋯ v_{n-1}`, and it is trivial if and only if `v ∉ L(X)`.

This module proves `PrintedLanguageReducesToWordProblem` along that route.
* `cylinderSymbols v` spells `∏_{t<n} u^{-t} e_{v_t} u^t` as a product of generator coefficients,
  through `e_{a v} = e_a · u⁻¹ e_v u`.
* `productWords` turns a product `s_1 ⋯ s_r s_0` into words for `e_12(s_1 ⋯ s_r s_0)` and
  `e_32(s_1 ⋯ s_r s_0)`, by the commutator identity `[e_ik(r), e_kj(s)] = e_ij(rs)`.
* `cylinderWord v` has value `e_12(e_[v])`, and `e_12(f) = 1` exactly when `f = 0`, that is, when
  the cylinder of `v` is empty.
* Both constructions are primitive recursive, so one query to the word problem decides `L(X)`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open Encodable Set SymbolicDynamics.FullShift
open scoped commutatorElement

namespace LanguageReduction

section Words

variable {A : Type}

/-- The pair of words for `e_12(s_0)` and `e_32(s_0)`. -/
def productWordsBase (s₀ : Coeff A) : List (Gen A × Bool) × List (Gen A × Bool) :=
  ([((⟨(0, 1), by decide⟩, s₀), true)], [((⟨(2, 1), by decide⟩, s₀), true)])

/-- From words for `e_12(t)` and `e_32(t)` to words for `e_12(ct)` and `e_32(ct)`. -/
def productWordsStep (c : Coeff A) (p : List (Gen A × Bool) × List (Gen A × Bool)) :
    List (Gen A × Bool) × List (Gen A × Bool) :=
  (wordComm [((⟨(0, 2), by decide⟩, c), true)] p.2, wordComm [((⟨(2, 0), by decide⟩, c), true)] p.1)

/-- Words for `e_12(s_1 ⋯ s_r s_0)` and `e_32(s_1 ⋯ s_r s_0)`. -/
def productWords (s₀ : Coeff A) : List (Coeff A) → List (Gen A × Bool) × List (Gen A × Bool)
  | [] => productWordsBase s₀
  | c :: l => productWordsStep c (productWords s₀ l)

/-- The coefficients of `∏_{t<n} u^{-t} e_{v_t} u^t`, through `e_{a v} = e_a · u⁻¹ e_v u`. -/
def cylinderSymbols : List A → List (Coeff A)
  | [] => []
  | a :: v => .letter a :: .uInv :: (cylinderSymbols v ++ [.u])

/-- A word for `e_12(∏_{t<n} u^{-t} e_{v_t} u^t)`: the symbols, then `u u⁻¹`. -/
def cylinderWord (v : List A) : List (Gen A × Bool) :=
  (productWords .uInv (cylinderSymbols v ++ [.u])).1

theorem productWords_eq_recOn (s₀ : Coeff A) (l : List (Coeff A)) :
    productWords s₀ l = List.recOn l (productWordsBase s₀) fun c _ IH => productWordsStep c IH := by
  induction l with
  | nil => rfl
  | cons c l ih => exact congrArg (productWordsStep c) ih

theorem cylinderSymbols_eq_recOn (v : List A) :
    cylinderSymbols v = List.recOn v [] fun a _ IH => Coeff.letter a :: Coeff.uInv :: (IH ++ [.u]) := by
  induction v with
  | nil => rfl
  | cons a v ih => exact congrArg (fun IH => Coeff.letter a :: Coeff.uInv :: (IH ++ [.u])) ih

end Words

section Values

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A] (S : Subshift A ℤ)

/-- `e_ij(a)` as an element of `G_X`. -/
noncomputable def elemG (i j : Fin 3) (h : i ≠ j) (a : R S) : G S :=
  ⟨elementaryUnit i j h a, elementaryUnit_mem _ _ _ _⟩

omit [DiscreteTopology A] [DecidableEq A] in
theorem elemG_eq_one_iff (i j : Fin 3) (h : i ≠ j) (a : R S) : elemG S i j h a = 1 ↔ a = 0 := by
  constructor
  · intro ha
    have hu : elementaryUnit i j h a = elementaryUnit i j h 0 := by
      rw [elementaryUnit_zero]
      exact congrArg Subtype.val ha
    exact elementaryUnit_injective i j h hu
  · rintro rfl
    exact Subtype.ext (elementaryUnit_zero i j h)

omit [DiscreteTopology A] [DecidableEq A] in
theorem elemG_comm {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R S) :
    elemG S i j hij a * elemG S j k hjk b * (elemG S i j hij a)⁻¹ * (elemG S j k hjk b)⁻¹ =
      elemG S i k hik (a * b) := by
  apply Subtype.ext
  change elementaryUnit i j hij a * elementaryUnit j k hjk b * (elementaryUnit i j hij a)⁻¹ *
      (elementaryUnit j k hjk b)⁻¹ = elementaryUnit i k hik (a * b)
  rw [← elementaryUnit_commutator i j k hij hjk hik a b, commutatorElement_def]

theorem genValue_mk (i j : Fin 3) (h : i ≠ j) (c : Coeff A) :
    genValue S (⟨(i, j), h⟩, c) = elemG S i j h (coeffValue S c) :=
  rfl

theorem wordValue_singleton_true {ι H : Type*} [Group H] (s : ι → H) (x : ι) :
    wordValue s [(x, true)] = s x := by
  simp [wordValue_cons, wordValue_nil]

theorem wordValue_productWords (s₀ : Coeff A) (l : List (Coeff A)) :
    wordValue (genValue S) (productWords s₀ l).1 =
        elemG S 0 1 (by decide) ((l.map (coeffValue S)).prod * coeffValue S s₀) ∧
      wordValue (genValue S) (productWords s₀ l).2 =
        elemG S 2 1 (by decide) ((l.map (coeffValue S)).prod * coeffValue S s₀) := by
  induction l with
  | nil =>
    simp only [productWords, productWordsBase, List.map_nil, List.prod_nil, one_mul,
      wordValue_singleton_true]
    exact ⟨rfl, rfl⟩
  | cons c l ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    simp only [productWords, productWordsStep]
    refine ⟨?_, ?_⟩
    · rw [wordValue_wordComm, ih₂, wordValue_singleton_true, genValue_mk,
        elemG_comm S (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide),
        List.map_cons, List.prod_cons, mul_assoc]
    · rw [wordValue_wordComm, ih₁, wordValue_singleton_true, genValue_mk,
        elemG_comm S (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide),
        List.map_cons, List.prod_cons, mul_assoc]

/-- `f ∘ T` for a locally constant function `f` on `X`. -/
noncomputable def shiftComap (f : LocallyConstant S.carrier (ZMod 2)) :
    LocallyConstant S.carrier (ZMod 2) :=
  LocallyConstant.comap ⟨⇑(subshiftHomeo S), (subshiftHomeo S).continuous⟩ f

/-- The indicator of the cylinder `{x : x_{[0,n)} = v}`. -/
noncomputable def cylinderIndicator : List A → LocallyConstant S.carrier (ZMod 2)
  | [] => 1
  | a :: v => letterIndicator S a * shiftComap S (cylinderIndicator v)

omit [DiscreteTopology A] [DecidableEq A] in
theorem shiftComap_apply (f : LocallyConstant S.carrier (ZMod 2)) (x : S.carrier) :
    shiftComap S f x = f ((subshiftHomeo S) x) := by
  simp [shiftComap, LocallyConstant.coe_comap]

omit [DiscreteTopology A] [DecidableEq A] in
theorem subshiftHomeo_apply_val (x : S.carrier) (n : ℤ) : ((subshiftHomeo S) x).1 n = x.1 (1 + n) :=
  rfl

theorem letterIndicator_apply (a : A) (x : S.carrier) :
    letterIndicator S a x = if x.1 0 = a then 1 else 0 :=
  rfl

/-- `u⁻¹ f u = f ∘ T`. -/
theorem unitInv_mul_coeff_mul_unit (f : LocallyConstant S.carrier (ZMod 2)) :
    coeffValue S .uInv * ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) f * coeffValue S .u =
      ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (shiftComap S f) := by
  have hf : LocallyConstant.comap ⟨⇑(subshiftHomeo S).symm, (subshiftHomeo S).symm.continuous⟩
      (shiftComap S f) = f := by
    ext x
    simp [shiftComap, LocallyConstant.coe_comap]
  calc coeffValue S .uInv * ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) f *
        coeffValue S .u
      = coeffValue S .uInv * (coeffValue S .u *
          ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (shiftComap S f)) := by
        simp only [coeffValue]
        rw [ClopenCrossedProduct.unit_mul_coeff, hf, mul_assoc]
    _ = ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (shiftComap S f) := by
        simp only [coeffValue]
        rw [← mul_assoc, Units.inv_mul, one_mul]

theorem prod_cylinderSymbols (v : List A) :
    ((cylinderSymbols v).map (coeffValue S)).prod =
      ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (cylinderIndicator S v) := by
  induction v with
  | nil => simp [cylinderSymbols, cylinderIndicator]
  | cons a v ih =>
    simp only [cylinderSymbols, cylinderIndicator, List.map_cons, List.map_append, List.map_nil,
      List.prod_cons, List.prod_append, List.prod_nil, mul_one, ih, map_mul,
      ← unitInv_mul_coeff_mul_unit]
    simp only [coeffValue, mul_assoc]

theorem wordValue_cylinderWord (v : List A) :
    wordValue (genValue S) (cylinderWord v) = elemG S 0 1 (by decide)
      (ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (cylinderIndicator S v)) := by
  rw [cylinderWord, (wordValue_productWords S _ _).1, List.map_append, List.prod_append,
    ← prod_cylinderSymbols]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, coeffValue,
    mul_assoc, Units.mul_inv]

theorem cylinderIndicator_apply (v : List A) (x : S.carrier) :
    cylinderIndicator S v x = if ∀ t : Fin v.length, x.1 ((t : ℕ) : ℤ) = v.get t then 1 else 0 := by
  induction v generalizing x with
  | nil => simp [cylinderIndicator]
  | cons a v ih =>
    have key : (∀ t : Fin (a :: v).length, x.1 ((t : ℕ) : ℤ) = (a :: v).get t) ↔
        x.1 0 = a ∧ ∀ t : Fin v.length, ((subshiftHomeo S) x).1 ((t : ℕ) : ℤ) = v.get t := by
      constructor
      · intro h
        refine ⟨h ⟨0, Nat.succ_pos _⟩, fun t => ?_⟩
        rw [subshiftHomeo_apply_val]
        simpa [add_comm] using h ⟨(t : ℕ) + 1, Nat.succ_lt_succ t.isLt⟩
      · rintro ⟨h0, hv⟩ ⟨t, ht⟩
        cases t with
        | zero => exact h0
        | succ t =>
          have h1 := hv ⟨t, Nat.lt_of_succ_lt_succ ht⟩
          rw [subshiftHomeo_apply_val] at h1
          simpa [add_comm] using h1
    simp only [cylinderIndicator, LocallyConstant.mul_apply, shiftComap_apply, ih,
      letterIndicator_apply, key]
    split_ifs <;> simp_all

theorem cylinderIndicator_eq_zero_iff (v : List A) :
    cylinderIndicator S v = 0 ↔ v ∉ language S := by
  constructor
  · rintro h ⟨x, hx, hxv⟩
    have hall : ∀ t : Fin v.length, x ((t : ℕ) : ℤ) = v.get t := fun t => by
      simpa [WordGraph.word] using congrFun hxv t
    have h1 : cylinderIndicator S v ⟨x, hx⟩ = 0 := by simp [h]
    have h2 : cylinderIndicator S v ⟨x, hx⟩ = 1 := by rw [cylinderIndicator_apply, if_pos hall]
    exact absurd (h2.symm.trans h1) (by decide)
  · intro h
    ext x
    have hn : ¬ ∀ t : Fin v.length, x.1 ((t : ℕ) : ℤ) = v.get t := fun hall =>
      h ⟨x.1, x.2, funext fun t => by simpa [WordGraph.word] using hall t⟩
    rw [cylinderIndicator_apply, if_neg hn]
    rfl

/-- The word for `e_12(e_[v])` is trivial exactly when `v ∉ L(X)`. -/
theorem wordValue_cylinderWord_eq_one_iff (v : List A) :
    wordValue (genValue S) (cylinderWord v) = 1 ↔ v ∉ language S := by
  rw [wordValue_cylinderWord, elemG_eq_one_iff,
    (ClopenCrossedProduct.coeff_injective (subshiftHomeo S) (ZMod 2)).eq_iff' (map_zero _),
    cylinderIndicator_eq_zero_iff]

end Values

section Primrec

variable {A : Type} [Primcodable A]

theorem primrec_coeff_letter : Primrec (Coeff.letter : A → Coeff A) :=
  ((Primrec.of_equiv_symm (e := Coeff.equivOption A)).comp
    (Primrec.option_some.comp Primrec.option_some)).of_eq fun _ => rfl

theorem primrec_wordInv {ι : Type*} [Primcodable ι] :
    Primrec (wordInv : List (ι × Bool) → List (ι × Bool)) := by
  have hg : Primrec₂ fun (_ : List (ι × Bool)) (x : ι × Bool) => (x.1, !x.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.not.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_reverse.comp (Primrec.list_map Primrec.id hg)).of_eq fun _ => rfl

theorem primrec₂_wordComm {ι : Type*} [Primcodable ι] :
    Primrec₂ (wordComm : List (ι × Bool) → List (ι × Bool) → List (ι × Bool)) := by
  have hinv := primrec_wordInv (ι := ι)
  exact (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp Primrec.fst Primrec.snd) (hinv.comp Primrec.fst))
    (hinv.comp Primrec.snd)).of_eq fun _ => rfl

theorem primrec_genSingleton (p : OffDiag) : Primrec fun c : Coeff A => [((p, c), true)] :=
  (Primrec.list_cons.comp (Primrec.pair (Primrec.pair (Primrec.const p) Primrec.id)
    (Primrec.const true)) (Primrec.const [])).of_eq fun _ => rfl

theorem primrec_productWords :
    Primrec fun q : Coeff A × List (Coeff A) => productWords q.1 q.2 := by
  have hg : Primrec fun q : Coeff A × List (Coeff A) => productWordsBase q.1 :=
    Primrec.pair ((primrec_genSingleton _).comp Primrec.fst)
      ((primrec_genSingleton _).comp Primrec.fst)
  have hh : Primrec₂ fun (_ : Coeff A × List (Coeff A))
      (p : Coeff A × List (Coeff A) × (List (Gen A × Bool) × List (Gen A × Bool))) =>
      productWordsStep p.1 p.2.2 :=
    Primrec.pair
      (primrec₂_wordComm.comp ((primrec_genSingleton _).comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (primrec₂_wordComm.comp ((primrec_genSingleton _).comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.list_rec Primrec.snd hg hh).of_eq fun q => (productWords_eq_recOn q.1 q.2).symm

theorem primrec_cylinderSymbols : Primrec (cylinderSymbols : List A → List (Coeff A)) := by
  have hh : Primrec₂ fun (_ : List A) (p : A × List A × List (Coeff A)) =>
      Coeff.letter p.1 :: Coeff.uInv :: (p.2.2 ++ [Coeff.u]) :=
    Primrec.list_cons.comp (primrec_coeff_letter.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.const Coeff.uInv)
        (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.const [Coeff.u])))
  exact (Primrec.list_rec Primrec.id (Primrec.const []) hh).of_eq fun v =>
    (cylinderSymbols_eq_recOn v).symm

theorem primrec_cylinderWord : Primrec (cylinderWord : List A → List (Gen A × Bool)) :=
  (Primrec.fst.comp (primrec_productWords.comp (Primrec.pair (Primrec.const Coeff.uInv)
    (Primrec.list_append.comp primrec_cylinderSymbols (Primrec.const [Coeff.u]))))).of_eq
    fun _ => rfl

end Primrec

end LanguageReduction

open LanguageReduction in
/-- **Proof, first paragraph.**  A word for `e_12(∏_{t<n} u^{-t} e_{v_t} u^t)` is computable from
`v`, and it is trivial if and only if `v ∉ L(X)`; so the word problem computes `L(X)`. -/
theorem printedLanguageReducesToWordProblem : PrintedLanguageReducesToWordProblem := by
  intro A _ _ _ _ _ S
  refine turingReducible_of_query
    (fun n => (wordProblemOracle (genValue S) n).get trivial) (fun _ => rfl)
    (fun n => encode (cylinderWord ((decode (α := List A) n).getD [])))
    (fun n m => cond (decode (α := List A) n).isSome (1 - m) 0)
    (Primrec.encode.comp (primrec_cylinderWord.comp
      (Primrec.option_getD.comp Primrec.decode (Primrec.const []))))
    (Primrec.cond (Primrec.option_isSome.comp (Primrec.decode.comp Primrec.fst))
      (Primrec.nat_sub.comp (Primrec.const 1) Primrec.snd) (Primrec.const 0))
    fun n => ?_
  cases hd : (decode n : Option (List A)) with
  | none => simp [languageOracle, hd]
  | some v =>
    by_cases hv : v ∈ language S
    · have hw : ¬ wordValue (genValue S) (cylinderWord v) = 1 := fun h =>
        (wordValue_cylinderWord_eq_one_iff S v).1 h hv
      simp [languageOracle, wordProblemOracle, hd, hv, hw]
    · have hw : wordValue (genValue S) (cylinderWord v) = 1 :=
        (wordValue_cylinderWord_eq_one_iff S v).2 hv
      simp [languageOracle, wordProblemOracle, hd, hv, hw]

#audit_closed_axioms printedLanguageReducesToWordProblem

end SimpleKazhdanSofic
end GroupApproximation
