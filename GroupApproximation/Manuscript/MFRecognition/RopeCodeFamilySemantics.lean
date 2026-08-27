import GroupApproximation.Manuscript.MFRecognition.RopeCodeFamilyConstruction

/-!
# `lem:finite-rope`, second sentence: the code presents `R̂_e`

The syntactic half is `RopeCodeFamilyConstruction`.  Here the code of `R̂_e`
built there is identified with `FiniteRope`, through
`Higman.MikhailovaRopeCodeSemantics.compileEquivToRope` at the benign
witness of `RopeObjects`:

* `keEquiv`: the ambient code presents `K_e`, by the product-code semantics
  and the free-group code semantics;
* `hcutting`: the cutting words generate exactly `L_e`, by
  `CentralRopeGenerators.Le_eq_closure_gens`;
* `hmarked`: the marked words spell `i(x), i(y), i(t)`;
* `hmarked_generates`: `x, y, t` generate `F`.

The result is `ropeCodeFamilyOf`: a `RopeCodeFamily` for the marked outputs
of any effective Higman compiler, which discharges the rope-code input of
`RecognitionAssembly`.
-/

namespace GroupApproximation

open PresentationCodes DirectProductCode DirectProductCodeSemantics
open BenignInfCodeSemantics Higman

/-- Product of isomorphisms, on a pair. -/
@[simp] theorem MulEquiv.prodCongr_apply' {M N M' N' : Type*}
    [MulOneClass M] [MulOneClass N] [MulOneClass M'] [MulOneClass N']
    (f : M ≃* M') (g : N ≃* N') (x : M) (y : N) :
    f.prodCongr g (x, y) = (f x, g y) := rfl

namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace RopeCodes

open FreeCodeSemantics
open MikhailovaRopeCode hiding Raw
open Rope Rope.RopeInput
open Assembly
open SecondLevelIndexSets

noncomputable section

variable {e : Nat.Partrec.Code} (o : MarkedHigmanOutput (qcodeSeed e))

/-! ## The ambient code presents `K_e` -/

/-- The pair factor `F(X_e) × F(X_e)`. -/
def pairEquiv :
    Carrier (productCode (hostFree o.raw) (hostFree o.raw)) ≃*
      FreeGroup (HostAlphabet o.host) × FreeGroup (HostAlphabet o.host) :=
  (productCodeEquiv (hostFree o.raw) (hostFree o.raw)).trans
    ((freeCodeEquiv o.host.1).prodCongr (freeCodeEquiv o.host.1))

/-- The code of `K⁰_e` presents `K⁰_e`. -/
def k0Equiv : Carrier (k0Code o.raw) ≃* K0 (ropeInputOf o) :=
  (productCodeEquiv F3 (productCode (hostFree o.raw) (hostFree o.raw))).trans
    ((freeCodeEquiv 2).prodCongr (pairEquiv o))

/-- The factor `P = F(x₁,y) × F(x₂,t)`. -/
def pEquiv : Carrier (productCode F2 F2) ≃* Ptarget :=
  (productCodeEquiv F2 F2).trans ((freeCodeEquiv 1).prodCongr (freeCodeEquiv 1))

/-- The code of `K^g` presents `K^g = F × P`. -/
def kgEquiv : Carrier kgCode ≃* Kg :=
  (productCodeEquiv F3 (productCode F2 F2)).trans ((freeCodeEquiv 2).prodCongr pEquiv)

/-- **The ambient code presents `K_e`.** -/
def keEquiv : Carrier (keCode o.raw) ≃* Ke (ropeInputOf o) :=
  (productCodeEquiv (k0Code o.raw) kgCode).trans ((k0Equiv o).prodCongr kgEquiv)

/-! ### Evaluating raw words

Each of the five product codes is read the same way: a left (respectively
right) word of the product code evaluates in the left (right) factor, and the
other coordinate is the identity.  The two lemmas below say this once, for an
arbitrary pair of factor identifications; every case is an instance. -/

theorem prodCongr_leftWord {A B : Type*} [Group A] [Group B]
    (c d : PresentationCode) (f : Carrier c ≃* A) (g : Carrier d ≃* B) (w : Raw) :
    (f.prodCongr g) (productCodeEquiv c d
        (evalWord (productCode c d) (leftWord c w))) = (f (evalWord c w), 1) := by
  rw [productCodeEquiv_eval_leftWord, MulEquiv.prodCongr_apply', map_one]

theorem prodCongr_rightWord {A B : Type*} [Group A] [Group B]
    (c d : PresentationCode) (f : Carrier c ≃* A) (g : Carrier d ≃* B) (w : Raw) :
    (f.prodCongr g) (productCodeEquiv c d
        (evalWord (productCode c d) (rightWord c d w))) = (1, g (evalWord d w)) := by
  rw [productCodeEquiv_eval_rightWord, MulEquiv.prodCongr_apply', map_one]

theorem keEquiv_k0Left (w : Raw) :
    keEquiv o (evalWord (keCode o.raw) (k0Left o.raw w))
      = (k0Equiv o (evalWord (k0Code o.raw) w), 1) :=
  prodCongr_leftWord (k0Code o.raw) kgCode (k0Equiv o) kgEquiv w

theorem keEquiv_kgRight (w : Raw) :
    keEquiv o (evalWord (keCode o.raw) (kgRight o.raw w))
      = (1, kgEquiv (evalWord kgCode w)) :=
  prodCongr_rightWord (k0Code o.raw) kgCode (k0Equiv o) kgEquiv w

theorem k0Equiv_src (w : Raw) :
    k0Equiv o (evalWord (k0Code o.raw) (leftWord F3 w)) = (wordOf F3 w, 1) :=
  prodCongr_leftWord F3 (productCode (hostFree o.raw) (hostFree o.raw))
    (freeCodeEquiv 2) (pairEquiv o) w

theorem k0Equiv_pair (w : Raw) :
    k0Equiv o (evalWord (k0Code o.raw)
        (rightWord F3 (productCode (hostFree o.raw) (hostFree o.raw)) w))
      = (1, pairEquiv o (evalWord (productCode (hostFree o.raw) (hostFree o.raw)) w)) :=
  prodCongr_rightWord F3 (productCode (hostFree o.raw) (hostFree o.raw))
    (freeCodeEquiv 2) (pairEquiv o) w

theorem pairEquiv_left (w : Raw) :
    pairEquiv o (evalWord (productCode (hostFree o.raw) (hostFree o.raw))
        (leftWord (hostFree o.raw) w))
      = (wordOf o.host w, 1) :=
  prodCongr_leftWord (hostFree o.raw) (hostFree o.raw)
    (freeCodeEquiv o.host.1) (freeCodeEquiv o.host.1) w

theorem pairEquiv_right (w : Raw) :
    pairEquiv o (evalWord (productCode (hostFree o.raw) (hostFree o.raw))
        (rightWord (hostFree o.raw) (hostFree o.raw) w))
      = (1, wordOf o.host w) :=
  prodCongr_rightWord (hostFree o.raw) (hostFree o.raw)
    (freeCodeEquiv o.host.1) (freeCodeEquiv o.host.1) w

theorem kgEquiv_src (w : Raw) :
    kgEquiv (evalWord kgCode (leftWord F3 w)) = (wordOf F3 w, 1) :=
  prodCongr_leftWord F3 (productCode F2 F2) (freeCodeEquiv 2) pEquiv w

theorem kgEquiv_P (w : Raw) :
    kgEquiv (evalWord kgCode (rightWord F3 (productCode F2 F2) w))
      = (1, pEquiv (evalWord (productCode F2 F2) w)) :=
  prodCongr_rightWord F3 (productCode F2 F2) (freeCodeEquiv 2) pEquiv w

theorem pEquiv_L (w : Raw) :
    pEquiv (evalWord (productCode F2 F2) (leftWord F2 w)) = (wordOf F2 w, 1) :=
  prodCongr_leftWord F2 F2 (freeCodeEquiv 1) (freeCodeEquiv 1) w

theorem pEquiv_R (w : Raw) :
    pEquiv (evalWord (productCode F2 F2) (rightWord F2 F2 w)) = (1, wordOf F2 w) :=
  prodCongr_rightWord F2 F2 (freeCodeEquiv 1) (freeCodeEquiv 1) w

/-- The generator words of the three-letter free code. -/
theorem wordOf_F3_gen (i : Fin 3) : wordOf F3 [((i : ℕ), true)] = FreeGroup.of i := by
  rw [RawWord.wordOf_pos]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem wordOf_F2_gen (i : Fin 2) : wordOf F2 [((i : ℕ), true)] = FreeGroup.of i := by
  rw [RawWord.wordOf_pos]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem wordOf_host_gen (i : Fin (genCount o.host)) :
    wordOf o.host [((i : ℕ), true)] = FreeGroup.of i := by
  rw [RawWord.wordOf_pos]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-- A generator word of the three-letter free code, at a raw index below the
alphabet size.  Stated so that the value already has the type `F` carries in
`K^g`, which keeps the product rewrites below type-correct. -/
theorem wordOf_F3_lt (i : ℕ) (h : i < 3) :
    wordOf F3 [(i, true)] = (FreeGroup.of ⟨i, h⟩ : Fxyt) := by
  rw [RawWord.wordOf_pos]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt h)

theorem wordOf_F2_lt (i : ℕ) (h : i < 2) :
    wordOf F2 [(i, true)] = (FreeGroup.of ⟨i, h⟩ : FreeGroup (Fin 2)) := by
  rw [RawWord.wordOf_pos]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt h)

theorem kgEquiv_gen (i : ℕ) (h : i < 3) :
    kgEquiv (evalWord kgCode (leftWord F3 [(i, true)])) = ((FreeGroup.of ⟨i, h⟩, 1) : Kg) := by
  rw [kgEquiv_src, wordOf_F3_lt i h]
  rfl

theorem k0Equiv_gen (i : ℕ) (h : i < 3) :
    k0Equiv o (evalWord (k0Code o.raw) (leftWord F3 [(i, true)]))
      = ((FreeGroup.of ⟨i, h⟩, 1) : K0 (ropeInputOf o)) := by
  rw [k0Equiv_src, wordOf_F3_lt i h]
  rfl

theorem pEquiv_L_gen (i : ℕ) (h : i < 2) :
    pEquiv (evalWord (productCode F2 F2) (leftWord F2 [(i, true)]))
      = ((FreeGroup.of ⟨i, h⟩, 1) : Ptarget) := by
  rw [pEquiv_L, wordOf_F2_lt i h]
  rfl

theorem pEquiv_R_gen (i : ℕ) (h : i < 2) :
    pEquiv (evalWord (productCode F2 F2) (rightWord F2 F2 [(i, true)]))
      = ((1, FreeGroup.of ⟨i, h⟩) : Ptarget) := by
  rw [pEquiv_R, wordOf_F2_lt i h]
  rfl

/-! ### The values of the cutting words -/

/-- The alphabet of the concrete rope input is the host alphabet. -/
abbrev hostIdx (z : (ropeInputOf o).X) : Fin (genCount o.host) := z

theorem jq_genX : jq (ropeInputOf o) (FreeGroup.of 0) = (Bridge.xTwo, Bridge.xTwo) :=
  Bridge.jQ_qx

theorem jq_genY : jq (ropeInputOf o) (FreeGroup.of 1) = (Bridge.yTwo, 1) :=
  Bridge.jQ_qy

theorem jq_genT : jq (ropeInputOf o) (FreeGroup.of 2) = ((1 : FreeGroup (Fin 2)), Bridge.yTwo) :=
  Bridge.jQ_qt

/-- The source cutting words evaluate to the basis of the first factor. -/
theorem value_sourceWord (i : Fin 3) :
    keEquiv o (evalWord (keCode o.raw) (k0Left o.raw
        (MikhailovaRankThreeCode.ambientSourceWord [((i : ℕ), true)])))
      = firstFactorHom (ropeInputOf o) (FreeGroup.of i) := by
  rw [keEquiv_k0Left]
  show (k0Equiv o (evalWord (k0Code o.raw) (leftWord F3 [((i : ℕ), true)])), 1) = _
  rw [k0Equiv_src, wordOf_F3_gen]
  rfl

/-- The diagonal cutting words evaluate to the diagonal generators of `M_e`. -/
theorem value_diagonalWord (z : Fin (genCount o.host)) :
    keEquiv o (evalWord (keCode o.raw) (k0Left o.raw
        (MikhailovaRankThreeCode.ambientPairWord o.raw
          (MikhailovaRankThreeCode.diagonalWord o.raw (z : ℕ)))))
      = mihailovaFactorHom (ropeInputOf o) (FreeGroup.of z, FreeGroup.of z) := by
  rw [keEquiv_k0Left]
  show (k0Equiv o (evalWord (k0Code o.raw)
      (rightWord F3 (productCode (hostFree o.raw) (hostFree o.raw))
        (leftWord (hostFree o.raw) [((z : ℕ), true)] ++
          rightWord (hostFree o.raw) (hostFree o.raw) [((z : ℕ), true)]))), 1) = _
  rw [k0Equiv_pair, evalWord_append, map_mul, pairEquiv_left, pairEquiv_right,
    wordOf_host_gen, Prod.mk_mul_mk, mul_one, one_mul]
  rfl

/-- The relator cutting words evaluate to the relator generators of `M_e`. -/
theorem value_relatorWord (rr : Raw) :
    keEquiv o (evalWord (keCode o.raw) (k0Left o.raw
        (MikhailovaRankThreeCode.ambientPairWord o.raw
          (MikhailovaRankThreeCode.pairLeftWord o.raw rr))))
      = mihailovaFactorHom (ropeInputOf o) (wordOf o.host rr, 1) := by
  rw [keEquiv_k0Left]
  show (k0Equiv o (evalWord (k0Code o.raw)
      (rightWord F3 (productCode (hostFree o.raw) (hostFree o.raw))
        (leftWord (hostFree o.raw) rr))), 1) = _
  rw [k0Equiv_pair, pairEquiv_left]
  rfl

theorem value_graphX :
    keEquiv o (evalWord (keCode o.raw) (kgRight o.raw (kgSrc 0 ++ kgP jqX)))
      = graphFactorHom (ropeInputOf o) (FreeGroup.of 0) := by
  rw [keEquiv_kgRight]
  show (1, kgEquiv (evalWord kgCode (leftWord F3 [(0, true)] ++
      rightWord F3 (productCode F2 F2) (leftWord F2 [(0, true)] ++ rightWord F2 F2 [(0, true)])))) = _
  rw [evalWord_append, map_mul, kgEquiv_gen 0 (by omega), kgEquiv_P, evalWord_append, map_mul,
    pEquiv_L_gen 0 (by omega), pEquiv_R_gen 0 (by omega)]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]
  rw [graphFactorHom_apply, jq_genX]
  rfl

theorem value_graphY :
    keEquiv o (evalWord (keCode o.raw) (kgRight o.raw (kgSrc 1 ++ kgP jqY)))
      = graphFactorHom (ropeInputOf o) (FreeGroup.of 1) := by
  rw [keEquiv_kgRight]
  show (1, kgEquiv (evalWord kgCode (leftWord F3 [(1, true)] ++
      rightWord F3 (productCode F2 F2) (leftWord F2 [(1, true)])))) = _
  rw [evalWord_append, map_mul, kgEquiv_gen 1 (by omega), kgEquiv_P,
    pEquiv_L_gen 1 (by omega)]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]
  rw [graphFactorHom_apply, jq_genY]
  rfl

theorem value_graphT :
    keEquiv o (evalWord (keCode o.raw) (kgRight o.raw (kgSrc 2 ++ kgP jqT)))
      = graphFactorHom (ropeInputOf o) (FreeGroup.of 2) := by
  rw [keEquiv_kgRight]
  show (1, kgEquiv (evalWord kgCode (leftWord F3 [(2, true)] ++
      rightWord F3 (productCode F2 F2) (rightWord F2 F2 [(1, true)])))) = _
  rw [evalWord_append, map_mul, kgEquiv_gen 2 (by omega), kgEquiv_P,
    pEquiv_R_gen 1 (by omega)]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]
  rw [graphFactorHom_apply, jq_genT]
  rfl

/-! ### The cutting words generate `L_e` -/

/-- Every cutting word evaluates to one of the printed generators of `L_e`. -/
theorem mem_gens_of_cutting {w : Raw} (hw : w ∈ cuttingWordsKe o.raw) :
    keEquiv o (evalWord (keCode o.raw) w) ∈
      firstFactorGens (ropeInputOf o) ∪ mihailovaGens (ropeInputOf o) ∪
        graphGens (ropeInputOf o) := by
  rcases List.mem_append.1 hw with hw | hw
  · obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
    rcases List.mem_append.1 hw0 with hw0 | hw0
    · rcases List.mem_append.1 hw0 with hw0 | hw0
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw0
        have hi3 : i < 3 := List.mem_range.1 hi
        refine Or.inl (Or.inl ⟨FreeGroup.of ⟨i, hi3⟩, ⟨⟨i, hi3⟩, rfl⟩, ?_⟩)
        exact (value_sourceWord o ⟨i, hi3⟩).symm
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw0
        have hig : i < genCount o.host := List.mem_range.1 hi
        refine Or.inl (Or.inr ⟨(FreeGroup.of ⟨i, hig⟩, FreeGroup.of ⟨i, hig⟩),
          Or.inl ⟨⟨i, hig⟩, rfl⟩, ?_⟩)
        exact (value_diagonalWord o ⟨i, hig⟩).symm
    · obtain ⟨rr, hrr, rfl⟩ := List.mem_map.1 hw0
      refine Or.inl (Or.inr ⟨(wordOf o.host rr, 1),
        Or.inr ⟨wordOf o.host rr, ?_, rfl⟩, ?_⟩)
      · show wordOf o.host rr ∈ hostRelators o.host
        exact List.mem_toFinset.2 (List.mem_map_of_mem hrr)
      · exact (value_relatorWord o rr).symm
  · simp only [graphWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact Or.inr ⟨FreeGroup.of 0, ⟨0, rfl⟩, (value_graphX o).symm⟩
    · exact Or.inr ⟨FreeGroup.of 1, ⟨1, rfl⟩, (value_graphY o).symm⟩
    · exact Or.inr ⟨FreeGroup.of 2, ⟨2, rfl⟩, (value_graphT o).symm⟩

/-- Every printed generator of `L_e` is the value of a cutting word. -/
theorem cutting_of_mem_gens {x : Ke (ropeInputOf o)}
    (hx : x ∈ firstFactorGens (ropeInputOf o) ∪ mihailovaGens (ropeInputOf o) ∪
      graphGens (ropeInputOf o)) :
    x ∈ keEquiv o '' (evalWord (keCode o.raw) '' {w | w ∈ cuttingWordsKe o.raw}) := by
  rcases hx with (⟨a, ⟨i, rfl⟩, rfl⟩ | ⟨m, hm, rfl⟩) | ⟨a, ⟨i, rfl⟩, rfl⟩
  · refine ⟨_, ⟨k0Left o.raw (MikhailovaRankThreeCode.ambientSourceWord [((i : ℕ), true)]),
      ?_, rfl⟩, value_sourceWord o i⟩
    show _ ∈ cuttingWordsKe o.raw
    refine List.mem_append_left _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨(i : ℕ), ?_, rfl⟩))
    exact List.mem_range.2 i.isLt
  · rcases hm with ⟨z, rfl⟩ | ⟨rr', hrr', rfl⟩
    · refine ⟨_, ⟨k0Left o.raw (MikhailovaRankThreeCode.ambientPairWord o.raw
        (MikhailovaRankThreeCode.diagonalWord o.raw (hostIdx o z : ℕ))), ?_, rfl⟩,
        value_diagonalWord o (hostIdx o z)⟩
      show _ ∈ cuttingWordsKe o.raw
      refine List.mem_append_left _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
      refine List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨(hostIdx o z : ℕ), ?_, rfl⟩))
      exact List.mem_range.2 (hostIdx o z).isLt
    · have hrr'' : rr' ∈ hostRelators o.host := hrr'
      obtain ⟨rr, hrr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hrr'')
      refine ⟨_, ⟨k0Left o.raw (MikhailovaRankThreeCode.ambientPairWord o.raw
        (MikhailovaRankThreeCode.pairLeftWord o.raw rr)), ?_, rfl⟩,
        value_relatorWord o rr⟩
      show _ ∈ cuttingWordsKe o.raw
      refine List.mem_append_left _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
      exact List.mem_append_right _ (List.mem_map.2 ⟨rr, hrr, rfl⟩)
  · fin_cases i
    · exact ⟨_, ⟨_, List.mem_append_right _ (by simp [graphWords]), rfl⟩, value_graphX o⟩
    · exact ⟨_, ⟨_, List.mem_append_right _ (by simp [graphWords]), rfl⟩, value_graphY o⟩
    · exact ⟨_, ⟨_, List.mem_append_right _ (by simp [graphWords]), rfl⟩, value_graphT o⟩

/-- The closure of the values of the cutting words is `L_e`. -/
theorem closure_cutting_eq :
    Subgroup.closure (keEquiv o '' (evalWord (keCode o.raw) '' {w | w ∈ cuttingWordsKe o.raw}))
      = Le (ropeInputOf o) := by
  rw [Le_eq_closure_gens]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact Subgroup.subset_closure (mem_gens_of_cutting o hw)
  · rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.subset_closure (cutting_of_mem_gens o hx)

/-- An equivalence carries closure membership across: `f a` lies in the
closure of `f '' S` exactly when `a` lies in the closure of `S`. -/
theorem mem_closure_image_equiv {G H : Type*} [Group G] [Group H]
    (f : G ≃* H) (S : Set G) (a : G) :
    f a ∈ Subgroup.closure (f '' S) ↔ a ∈ Subgroup.closure S := by
  have hmap : Subgroup.closure (f '' S) = (Subgroup.closure S).map f.toMonoidHom := by
    rw [MonoidHom.map_closure]
    rfl
  rw [hmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- The source subgroup of the central edges is generated by the values of
the cutting words. -/
theorem range_srcGen_centralEdges (c : PresentationCode) (L : List Raw) :
    Set.range (HNNPresentation.srcGen (codeRels c)
        (FreeEdgeTowerSemantics.sourceWord c (FreeEdgeTowerCode.centralEdges L)))
      = evalWord c '' {w | w ∈ L} := by
  have hlen : (FreeEdgeTowerCode.centralEdges L).length = L.length := by
    simp [FreeEdgeTowerCode.centralEdges]
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    have hmem : (FreeEdgeTowerCode.centralEdges L).get i ∈ FreeEdgeTowerCode.centralEdges L := by
      rw [List.get_eq_getElem]
      exact List.getElem_mem _
    obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hmem
    refine ⟨w, hw, ?_⟩
    show evalWord c w
      = PresentedGroup.mk (codeRels c) (wordOf c ((FreeEdgeTowerCode.centralEdges L).get i).1)
    rw [← hwe]
    rfl
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hw
    have hn : (i : ℕ) < (FreeEdgeTowerCode.centralEdges L).length := by
      rw [hlen]; exact i.isLt
    have hval : ((FreeEdgeTowerCode.centralEdges L).get ⟨(i : ℕ), hn⟩).1 = w := by
      simpa [FreeEdgeTowerCode.centralEdges, List.get_eq_getElem] using hi
    refine ⟨⟨(i : ℕ), hn⟩, ?_⟩
    show PresentedGroup.mk (codeRels c)
        (wordOf c ((FreeEdgeTowerCode.centralEdges L).get ⟨(i : ℕ), hn⟩).1) = evalWord c w
    rw [hval]
    rfl

/-- **The cutting words generate `L_e`**: the hypothesis `hcutting` of
`compileEquivToRope`. -/
theorem hcutting (g : Carrier (keCode o.raw)) :
    g ∈ HNNPresentation.srcSub (codeRels (keCode o.raw))
        (FreeEdgeTowerSemantics.sourceWord (keCode o.raw)
          (FreeEdgeTowerCode.centralEdges (cuttingWordsKe o.raw))) ↔
      keEquiv o g ∈ (witness (ropeInputOf o)).L := by
  show g ∈ Subgroup.closure (Set.range (HNNPresentation.srcGen _ _)) ↔
    keEquiv o g ∈ Le (ropeInputOf o)
  rw [range_srcGen_centralEdges, ← closure_cutting_eq o,
    mem_closure_image_equiv (keEquiv o)]

/-! ### The marked words -/

/-- The three marked source words name `x, y, t`. -/
theorem markedValue_gen (i : ℕ) (h : i < 3) (u : Raw) :
    MikhailovaRopeCodeSemantics.markedValue F3 (freeCodeEquiv 2) ([(i, true)], u)
      = (FreeGroup.of ⟨i, h⟩ : Fxyt) :=
  wordOf_F3_lt i h

/-- The `K⁰_e` half of a marked word: the source letter in the first factor
and the marked host word in the first free host factor. -/
theorem k0Equiv_marked (i : ℕ) (h : i < 3) (w : Raw) :
    k0Equiv o (evalWord (k0Code o.raw)
        (leftWord F3 [(i, true)] ++
          rightWord F3 (productCode (hostFree o.raw) (hostFree o.raw))
            (leftWord (hostFree o.raw) w)))
      = (((FreeGroup.of ⟨i, h⟩ : Fxyt), (wordOf o.host w, 1)) : K0 (ropeInputOf o)) := by
  rw [evalWord_append, map_mul, k0Equiv_gen o i h, k0Equiv_pair, pairEquiv_left]
  exact Prod.ext (mul_one _) (one_mul _)

/-- The marked words evaluate to `i(x), i(y), i(t)`. -/
theorem value_marked (i : ℕ) (h : i < 3) (w : Raw) :
    keEquiv o (evalWord (keCode o.raw) (markedKe o.raw i
        (MikhailovaRankThreeCode.markedAmbientWord o.raw i w)))
      = (((FreeGroup.of ⟨i, h⟩, (wordOf o.host w, 1)), (FreeGroup.of ⟨i, h⟩, 1)) :
          Ke (ropeInputOf o)) := by
  show keEquiv o (evalWord (keCode o.raw)
    (k0Left o.raw (leftWord F3 [(i, true)] ++
        rightWord F3 (productCode (hostFree o.raw) (hostFree o.raw))
          (leftWord (hostFree o.raw) w)) ++
      kgRight o.raw (leftWord F3 [(i, true)]))) = _
  rw [evalWord_append, map_mul, keEquiv_k0Left, keEquiv_kgRight,
    k0Equiv_marked o i h w, kgEquiv_gen i h]
  exact Prod.ext (mul_one _) (one_mul _)

/-- The marked homomorphism on the generators. -/
theorem markedWord_gen_zero : o.markedWord (FreeGroup.of 0) = wordOf o.host o.wordX := by
  rw [MarkedHigmanOutput.markedWord, markedHom_apply_of]
  simp

theorem markedWord_gen_one : o.markedWord (FreeGroup.of 1) = wordOf o.host o.wordY := by
  rw [MarkedHigmanOutput.markedWord, markedHom_apply_of]
  simp

theorem markedWord_gen_two : o.markedWord (FreeGroup.of 2) = wordOf o.host o.wordT := by
  rw [MarkedHigmanOutput.markedWord, markedHom_apply_of]
  simp

/-- `i(a) = ((a, w_a, 1), (a, 1))`, for the concrete rope input. -/
@[simp] theorem iEmb_ropeInputOf (f : Fxyt) :
    iEmb (ropeInputOf o) f = ((f, (o.markedWord f, 1)), (f, 1)) := rfl

/-- **The marked words spell `i(x), i(y), i(t)`**: the hypothesis `hmarked` of
`compileEquivToRope`. -/
theorem hmarked (p : Raw × Raw) (hp : p ∈ markedList o.raw) :
    keEquiv o (PresentedGroup.mk (codeRels (keCode o.raw)) (wordOf (keCode o.raw) p.2))
      = (witness (ropeInputOf o)).emb
          (MikhailovaRopeCodeSemantics.markedValue F3 (freeCodeEquiv 2) p) := by
  have key : ∀ (i : ℕ) (h : i < 3) (u v : Raw),
      o.markedWord (FreeGroup.of ⟨i, h⟩) = wordOf o.host u →
      keEquiv o (evalWord (keCode o.raw)
          (markedKe o.raw i (MikhailovaRankThreeCode.markedAmbientWord o.raw i u)))
        = iEmb (ropeInputOf o)
            (MikhailovaRopeCodeSemantics.markedValue F3 (freeCodeEquiv 2) ([(i, true)], v)) := by
    intro i h u v hu
    rw [value_marked o i h u, markedValue_gen i h v, iEmb_ropeInputOf, hu]
    rfl
  simp only [markedList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact key 0 (by omega) o.wordX _ (markedWord_gen_zero o)
  · exact key 1 (by omega) o.wordY _ (markedWord_gen_one o)
  · exact key 2 (by omega) o.wordT _ (markedWord_gen_two o)

/-- **`x, y, t` generate `F`**: the hypothesis `hmarked_generates` of
`compileEquivToRope`. -/
theorem hmarked_generates :
    Subgroup.closure
      (MikhailovaRopeCodeSemantics.markedSet F3 (freeCodeEquiv 2) (markedList o.raw)) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← closure_basisXYT]
  apply Subgroup.closure_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨([(0, true)], markedKe o.raw 0 (MikhailovaRankThreeCode.markedZero o.raw)),
      by simp [markedList], markedValue_gen 0 (by omega) _⟩
  · exact ⟨([(1, true)], markedKe o.raw 1 (MikhailovaRankThreeCode.markedOne o.raw)),
      by simp [markedList], markedValue_gen 1 (by omega) _⟩
  · exact ⟨([(2, true)], markedKe o.raw 2 (MikhailovaRankThreeCode.markedTwo o.raw)),
      by simp [markedList], markedValue_gen 2 (by omega) _⟩

/-! ## The code presents `R̂_e` -/

/-- **`lem:finite-rope`, second sentence, semantically**: the compiled code
presents `R̂_e`. -/
def ropeCodeEquiv : Carrier (ropeCode o.raw) ≃* FiniteRope (ropeInputOf o) :=
  (MikhailovaRopeCodeSemantics.compileEquivToRope (witness (ropeInputOf o)) (keCode o.raw) F3
    (cuttingWordsKe o.raw) (markedList o.raw) (keEquiv o) (freeCodeEquiv 2) (hcutting o)
    (hmarked o) (hmarked_generates o)).trans (finiteRopeEquiv (ropeInputOf o)).symm

/-- **The rope codes of any effective Higman compiler.**  This discharges the
`RopeCodeFamily` input of `RecognitionAssembly`. -/
def ropeCodeFamilyOf (h : EffectiveHigmanCompiler) : RopeCodeFamily (markedOutputsOfCompiler h) where
  code e := ropeCode (h.compile (qcodeSeed e))
  computable_code := computable_ropeCode.comp (h.computable.comp computable_qcodeSeed)
  equiv e := by
    have hraw : (markedOutputsOfCompiler h e).raw = h.compile (qcodeSeed e) :=
      (h.marks (qcodeSeed e)).choose_spec
    rw [← hraw]
    exact ropeCodeEquiv (markedOutputsOfCompiler h e)

end

end RopeCodes
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
