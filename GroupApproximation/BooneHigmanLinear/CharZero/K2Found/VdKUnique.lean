import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKBar
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKPerfect
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.ProdSigma

/-!
# vdK 3.17–3.22: the elements `X(i, j)` and Theorem 1 (k2-poly, piece F.1)

W. van der Kallen, *Another presentation for Steinberg groups*, Indag. Math. **39** (1977),
3.17–3.22. Throughout, `4 ≤ n = |I|`.

For `k i = 1` and `j i = 0`, vdK 3.1 writes `j = Σ w_pq` with `w_pq` a multiple of a basic row;
in ordered-pair form these are `vdkPiece i j k p q` (VdKPerfect), here `piece i j k (p, q)`.

* `xz_eq_prod_pairsAll`, `xz_mem_Xbar_of_two_zeros` (**vdK 3.18**): if `j` has two zeros `a ≠ b`,
  then `x(i, j)` is the product of the `x(i, w_pq)` in vdK's order (first the pairs `(p, a)`, then
  the pairs `(p, b)`, then the rest), so `x(i, j) ∈ X̄(i, j)`.
* `xz_commute` (**vdK 3.19**): `x(i, j)` and `x(i, k)` commute when `j` and `k` each have at most
  two nonzero coordinates. Without a common zero this is `conj_xz_of_two_zeros`, which uses 3.14,
  3.15 and 3.18 for two columns with a coordinate `1`.
* `xk` (**vdK 3.20**): `x_i(j; k)`, the product of all `x(i, w_pq)` (order-free by 3.19);
  `xk_add`: `x_i(u; k) x_i(v; k) = x_i(u + v; k)`; `xz_eq_xk`: `x(i, j) = x_i(j; k)` when `j` has
  two zeros.
* `eq_xk_of_mem_Xbar` (**vdK 3.21**): `X̄(i, j) = {x_i(j; k)}`.
* `elements` (**vdK 3.22**): the elements `X(i, j)` satisfy vdK's requirements 3.6, so `theorem1`
  (vdK's Theorem 1, `Theorem1At I A`) holds for `4 ≤ n`. `elements_elt_eq_xvw`: for `w` with two
  zeros, `X(v, w)` is the elementary `x(v, w)` of vdK 3.10 at either zero.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace VdK

open scoped commutatorElement Matrix
open GroupApproximation.SteinbergGroup

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

/-! ### Lists of rows -/

theorem list_sum_apply_eq_zero {L : List (I → A)} {t : I} (h : ∀ w ∈ L, w t = 0) :
    L.sum t = 0 := by
  induction L with
  | nil => rfl
  | cons w L ih =>
    rw [List.sum_cons, Pi.add_apply, h w (List.mem_cons.2 (Or.inl rfl)),
      ih (fun w' h' => h w' (List.mem_cons.2 (Or.inr h'))), add_zero]

theorem list_sum_dotProduct_eq_zero {L : List (I → A)} {i : I → A} (h : ∀ w ∈ L, w ⬝ᵥ i = 0) :
    L.sum ⬝ᵥ i = 0 := by
  induction L with
  | nil => exact zero_dotProduct i
  | cons w L ih =>
    rw [List.sum_cons, add_dotProduct, h w (List.mem_cons.2 (Or.inl rfl)),
      ih (fun w' h' => h w' (List.mem_cons.2 (Or.inr h'))), add_zero]

/-- vdK 3.11, iterated: rows that all vanish at `a ≠ b` multiply like their sum. -/
theorem prod_xz_of_zeros {i : I → A} {a b : I} (hab : a ≠ b) :
    ∀ L : List (I → A), (∀ w ∈ L, w ⬝ᵥ i = 0 ∧ w a = 0 ∧ w b = 0) →
      (L.map (xz i)).prod = xz i L.sum := by
  intro L
  induction L with
  | nil =>
    intro _
    rw [List.map_nil, List.prod_nil, List.sum_nil, xz_zero]
  | cons w L ih =>
    intro hL
    have hL' : ∀ w' ∈ L, w' ⬝ᵥ i = 0 ∧ w' a = 0 ∧ w' b = 0 :=
      fun w' h' => hL w' (List.mem_cons.2 (Or.inr h'))
    obtain ⟨h1, h2, h3⟩ := hL w (List.mem_cons.2 (Or.inl rfl))
    rw [List.map_cons, List.prod_cons, List.sum_cons, ih hL']
    exact xz_add (p := a) (q := b) (r := b) hab.symm hab.symm h1
      (list_sum_dotProduct_eq_zero fun w' h' => (hL' w' h').1) h2 h3
      (list_sum_apply_eq_zero fun w' h' => (hL' w' h').2.1)
      (list_sum_apply_eq_zero fun w' h' => (hL' w' h').2.2)

/-- vdK 3.18, one group of factors: rows `f p` supported on `{p, a}`, with `f a = f b = 0`. -/
theorem prod_xz_group (h4 : 4 ≤ Fintype.card I) {i : I → A} {a b : I} (hab : a ≠ b)
    (f : I → I → A) (hfi : ∀ p, f p ⬝ᵥ i = 0) (hf : ∀ p t, t ≠ p → t ≠ a → f p t = 0)
    (hf0 : ∀ p, p = a ∨ p = b → f p = 0) :
    ∀ ps : List I, ps.Nodup → (ps.map fun p => xz i (f p)).prod = xz i (ps.map f).sum := by
  have hfb : ∀ p, f p b = 0 := by
    intro p
    by_cases hpb : p = b
    · rw [hf0 p (Or.inr hpb), Pi.zero_apply]
    · exact hf p b (Ne.symm hpb) (Ne.symm hab)
  intro ps
  induction ps with
  | nil =>
    intro _
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil, xz_zero]
  | cons p ps ih =>
    intro hnd
    obtain ⟨hp, hnd'⟩ := List.nodup_cons.1 hnd
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, ih hnd']
    by_cases hpab : p = a ∨ p = b
    · rw [hf0 p hpab, xz_zero, one_mul, zero_add]
    · push_neg at hpab
      obtain ⟨t, htp, hta, htb⟩ := exists_ne_three h4 p a b
      have hsp : (ps.map f).sum p = 0 := list_sum_apply_eq_zero fun w hw => by
        obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hw
        exact hf p' p (fun h => hp (h ▸ hp')) hpab.1
      exact xz_add (p := b) (q := p) (r := t) htb hpab.2 (hfi p)
        (list_sum_dotProduct_eq_zero fun w hw => by
          obtain ⟨p', -, rfl⟩ := List.mem_map.1 hw
          exact hfi p')
        (hfb p) (hf p t htp hta)
        (list_sum_apply_eq_zero fun w hw => by
          obtain ⟨p', -, rfl⟩ := List.mem_map.1 hw
          exact hfb p')
        hsp

/-! ### vdK's order of the pairs -/

/-- `I \ {a, b}`. -/
def rest2 (a b : I) : Finset I :=
  (Finset.univ.erase a).erase b

theorem mem_rest2 {a b t : I} : t ∈ rest2 a b ↔ t ≠ b ∧ t ≠ a := by
  simp [rest2, Finset.mem_erase]

/-- The pairs `(p, q)` for all `p`. -/
def pairsAt (q : I) : List (I × I) :=
  (Finset.univ : Finset I).toList.map fun p => (p, q)

/-- The pairs `(p, q)` with `q ∉ {a, b}`. -/
def pairsRest (a b : I) : List (I × I) :=
  (Finset.univ : Finset I).toList ×ˢ (rest2 a b).toList

/-- All pairs, in vdK's order for 3.18. -/
def pairsAll (a b : I) : List (I × I) :=
  pairsAt a ++ pairsAt b ++ pairsRest a b

theorem mem_pairsAt {q : I} (x : I × I) : x ∈ pairsAt q ↔ x.2 = q := by
  constructor
  · intro h
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 h
    rfl
  · intro h
    exact List.mem_map.2 ⟨x.1, Finset.mem_toList.2 (Finset.mem_univ _), Prod.ext rfl h.symm⟩

theorem mem_pairsRest {a b : I} (x : I × I) : x ∈ pairsRest a b ↔ x.2 ≠ b ∧ x.2 ≠ a := by
  rcases x with ⟨p, q⟩
  rw [pairsRest, List.mem_product, Finset.mem_toList, Finset.mem_toList, mem_rest2]
  simp

theorem nodup_pairsAt (q : I) : (pairsAt q).Nodup := by
  unfold pairsAt
  refine (Finset.nodup_toList _).map ?_
  intro p p' h
  exact congrArg Prod.fst h

theorem nodup_pairsAll {a b : I} (hab : a ≠ b) : (pairsAll a b).Nodup := by
  refine List.Nodup.append (List.Nodup.append (nodup_pairsAt a) (nodup_pairsAt b) ?_)
    ((Finset.nodup_toList _).product (Finset.nodup_toList _)) ?_
  · intro x hxa hxb
    exact hab (((mem_pairsAt x).1 hxa).symm.trans ((mem_pairsAt x).1 hxb))
  · intro x hx hr
    have hr' := (mem_pairsRest x).1 hr
    rcases List.mem_append.1 hx with h | h
    · exact hr'.2 ((mem_pairsAt x).1 h)
    · exact hr'.1 ((mem_pairsAt x).1 h)

theorem mem_pairsAll {a b : I} (x : I × I) : x ∈ pairsAll a b := by
  by_cases ha : x.2 = a
  · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl ((mem_pairsAt x).2 ha))))
  by_cases hb : x.2 = b
  · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ((mem_pairsAt x).2 hb))))
  exact List.mem_append.2 (Or.inr ((mem_pairsRest x).2 ⟨hb, ha⟩))

theorem toFinset_pairsAll (a b : I) : (pairsAll a b).toFinset = Finset.univ :=
  Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (mem_pairsAll x)

/-! ### vdK 3.18 -/

/-- `w_pq` as a function of the pair `(p, q)`. -/
abbrev piece (i j k : I → A) (x : I × I) : I → A :=
  vdkPiece i j k x.1 x.2

theorem piece_isBasic (i j k : I → A) (x : I × I) : IsBasic i (piece i j k x) :=
  ⟨j x.1 * k x.2, x.1, x.2, rfl⟩

theorem vdkPiece_of_apply_eq_zero {i j k : I → A} {p : I} (hjp : j p = 0) (q : I) :
    vdkPiece i j k p q = 0 := by
  rw [vdkPiece, hjp, zero_mul, zero_smul]

theorem map_map_xz (i j k : I → A) (L : List (I × I)) :
    (L.map (piece i j k)).map (xz i) = L.map fun x => xz i (piece i j k x) := by
  induction L with
  | nil => rfl
  | cons x L ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]

theorem sum_pairsAll {i j k : I → A} (hji : j ⬝ᵥ i = 0) (hk : k ⬝ᵥ i = 1) {a b : I}
    (hab : a ≠ b) : ((pairsAll a b).map (piece i j k)).sum = j := by
  rw [← List.sum_toFinset _ (nodup_pairsAll hab), toFinset_pairsAll, Fintype.sum_prod_type]
  exact sum_vdkPiece hji hk

/-- **vdK 3.18.** If `j i = 0`, `k i = 1` and `j_a = j_b = 0` with `a ≠ b`, then `x(i, j)` is the
product of the `x(i, w_pq)` in vdK's order. -/
theorem xz_eq_prod_pairsAll (h4 : 4 ≤ Fintype.card I) {i j k : I → A} (hji : j ⬝ᵥ i = 0)
    (hk : k ⬝ᵥ i = 1) {a b : I} (hab : a ≠ b) (hja : j a = 0) (hjb : j b = 0) :
    ((pairsAll a b).map fun x => xz i (piece i j k x)).prod = xz i j := by
  have hzero : ∀ p, p = a ∨ p = b → ∀ q, vdkPiece i j k p q = 0 := by
    rintro p (h | h) q
    · rw [h]
      exact vdkPiece_of_apply_eq_zero hja q
    · rw [h]
      exact vdkPiece_of_apply_eq_zero hjb q
  have hA := prod_xz_group h4 hab (fun p => vdkPiece i j k p a)
    (fun p => vdkPiece_dotProduct i j k p a)
    (fun p t htp hta => vdkPiece_apply_of_ne i j k htp hta)
    (fun p hp => hzero p hp a) (Finset.univ : Finset I).toList (Finset.nodup_toList _)
  have hB := prod_xz_group h4 hab.symm (fun p => vdkPiece i j k p b)
    (fun p => vdkPiece_dotProduct i j k p b)
    (fun p t htp htb => vdkPiece_apply_of_ne i j k htp htb)
    (fun p hp => hzero p hp.symm b) (Finset.univ : Finset I).toList (Finset.nodup_toList _)
  have hrest : ∀ w ∈ (pairsRest a b).map (piece i j k), w ⬝ᵥ i = 0 ∧ w a = 0 ∧ w b = 0 := by
    intro w hw
    obtain ⟨⟨p, q⟩, hx, rfl⟩ := List.mem_map.1 hw
    have hq := (mem_pairsRest (p, q)).1 hx
    have hz : ∀ t, t = a ∨ t = b → vdkPiece i j k p q t = 0 := by
      intro t ht
      by_cases htp : t = p
      · rw [hzero p (htp ▸ ht) q, Pi.zero_apply]
      · refine vdkPiece_apply_of_ne i j k htp ?_
        rintro rfl
        rcases ht with rfl | rfl
        · exact hq.2 rfl
        · exact hq.1 rfl
    exact ⟨vdkPiece_dotProduct i j k p q, hz a (Or.inl rfl), hz b (Or.inr rfl)⟩
  have hR := prod_xz_of_zeros hab _ hrest
  rw [map_map_xz] at hR
  obtain ⟨Ga, hGa⟩ : ∃ G : I → A,
      G = ((Finset.univ : Finset I).toList.map fun p => vdkPiece i j k p a).sum := ⟨_, rfl⟩
  obtain ⟨Gb, hGb⟩ : ∃ G : I → A,
      G = ((Finset.univ : Finset I).toList.map fun p => vdkPiece i j k p b).sum := ⟨_, rfl⟩
  obtain ⟨Gr, hGr⟩ : ∃ G : I → A, G = ((pairsRest a b).map (piece i j k)).sum := ⟨_, rfl⟩
  have hsum : Ga + Gb + Gr = j := by
    have h := sum_pairsAll hji hk hab
    rw [pairsAll, List.map_append, List.map_append, List.sum_append, List.sum_append, pairsAt,
      pairsAt, List.map_map, List.map_map] at h
    rw [hGa, hGb, hGr]
    exact h
  have hGab : Ga b = 0 := by
    rw [hGa]
    exact list_sum_apply_eq_zero fun w hw => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
      by_cases hpb : p = b
      · rw [hzero p (Or.inr hpb) a, Pi.zero_apply]
      · exact vdkPiece_apply_of_ne i j k (Ne.symm hpb) (Ne.symm hab)
  have hGba : Gb a = 0 := by
    rw [hGb]
    exact list_sum_apply_eq_zero fun w hw => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
      by_cases hpa : p = a
      · rw [hzero p (Or.inl hpa) b, Pi.zero_apply]
      · exact vdkPiece_apply_of_ne i j k (Ne.symm hpa) hab
  have hGra : Gr a = 0 := by
    rw [hGr]
    exact list_sum_apply_eq_zero fun w hw => (hrest w hw).2.1
  have hGrb : Gr b = 0 := by
    rw [hGr]
    exact list_sum_apply_eq_zero fun w hw => (hrest w hw).2.2
  have hGaa : Ga a = 0 := by
    have h := congrFun hsum a
    rw [Pi.add_apply, Pi.add_apply, hGba, hGra, add_zero, add_zero, hja] at h
    exact h
  have hGbb : Gb b = 0 := by
    have h := congrFun hsum b
    rw [Pi.add_apply, Pi.add_apply, hGab, hGrb, add_zero, zero_add, hjb] at h
    exact h
  have hGai : Ga ⬝ᵥ i = 0 := by
    rw [hGa]
    exact list_sum_dotProduct_eq_zero fun w hw => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
      exact vdkPiece_dotProduct i j k p a
  have hGbi : Gb ⬝ᵥ i = 0 := by
    rw [hGb]
    exact list_sum_dotProduct_eq_zero fun w hw => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
      exact vdkPiece_dotProduct i j k p b
  have hGri : Gr ⬝ᵥ i = 0 := by
    rw [hGr]
    exact list_sum_dotProduct_eq_zero fun w hw => (hrest w hw).1
  have hab1 : xz i Ga * xz i Gb = xz i (Ga + Gb) :=
    xz_add (p := a) (q := b) (r := b) hab.symm hab.symm hGai hGbi hGaa hGab hGba hGbb
  have hab2 : xz i (Ga + Gb) * xz i Gr = xz i (Ga + Gb + Gr) :=
    xz_add (p := a) (q := b) (r := b) hab.symm hab.symm
      (by rw [add_dotProduct, hGai, hGbi, add_zero]) hGri
      (by rw [Pi.add_apply, hGaa, hGba, add_zero]) (by rw [Pi.add_apply, hGab, hGbb, add_zero])
      hGra hGrb
  have eA : ((pairsAt a).map fun x => xz i (piece i j k x)).prod = xz i Ga := by
    rw [hGa, pairsAt, List.map_map]
    exact hA
  have eB : ((pairsAt b).map fun x => xz i (piece i j k x)).prod = xz i Gb := by
    rw [hGb, pairsAt, List.map_map]
    exact hB
  have eR : ((pairsRest a b).map fun x => xz i (piece i j k x)).prod = xz i Gr := by
    rw [hGr]
    exact hR
  rw [pairsAll, List.map_append, List.map_append, List.prod_append, List.prod_append, eA, eB, eR,
    hab1, hab2, hsum]

#audit_axioms xz_eq_prod_pairsAll

/-- **vdK 3.18.** `x(i, j) ∈ X̄(i, j)` when `j` has two zeros (and `k i = 1`). -/
theorem xz_mem_Xbar_of_two_zeros (h4 : 4 ≤ Fintype.card I) {i j k : I → A} (hji : j ⬝ᵥ i = 0)
    (hk : k ⬝ᵥ i = 1) {a b : I} (hab : a ≠ b) (hja : j a = 0) (hjb : j b = 0) :
    xz i j ∈ Xbar i j := by
  refine mem_Xbar.2 ⟨(pairsAll a b).map (piece i j k), ?_, sum_pairsAll hji hk hab, ?_⟩
  · intro w hw
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hw
    exact piece_isBasic i j k x
  · rw [map_map_xz]
    exact xz_eq_prod_pairsAll h4 hji hk hab hja hjb

/-! ### vdK 3.19 -/

theorem unimod_col (z : SteinbergGroup I A) (r : I) :
    (Pi.single r (1 : A) ᵥ* matInv z) ⬝ᵥ (mat z *ᵥ Pi.single r 1) = 1 := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, matInv_mul_mat, Matrix.one_mulVec,
    single_dotProduct, Pi.single_eq_same, mul_one]

theorem mat_colProd_eq (r : I) (i : I → A) :
    mat (colProd r i) = 1 + Matrix.vecMulVec (i - Pi.single r (i r)) (Pi.single r 1) := by
  show ((stU I A (colProd r i) : (Matrix I I A)ˣ) : Matrix I I A) = _
  rw [stU_apply, mat_colProd]
  rfl

/-- A column with `v_r = 1` is `π(x(v)_r) ε_r`. -/
theorem mat_colProd_mulVec_single {v : I → A} {r : I} (hv : v r = 1) :
    mat (colProd r v) *ᵥ Pi.single r 1 = v := by
  rw [mat_colProd_eq, one_add_vecMulVec_mulVec, single_dotProduct, Pi.single_eq_same, mul_one,
    one_smul, hv, add_sub_cancel]

/-- vdK 3.19, the key step: `Y x(v, j) Y⁻¹ = x(π(Y) v, j)` for a column `v` with a coordinate `1`,
when `j` has two zeros and `j π(Y)⁻¹ = j`. -/
theorem conj_xz_col (h4 : 4 ≤ Fintype.card I) {j v : I → A} {r : I} (hvr : v r = 1)
    (hjv : j ⬝ᵥ v = 0) {t1 t2 : I} (ht : t1 ≠ t2) (hj1 : j t1 = 0) (hj2 : j t2 = 0)
    (Y : SteinbergGroup I A) (hYj : j ᵥ* matInv Y = j) :
    Y * xz v j * Y⁻¹ = xz (mat Y *ᵥ v) j := by
  have hz := mat_colProd_mulVec_single hvr
  have hkv := unimod_col (colProd r v) r
  rw [hz] at hkv
  have h1 := conj_mem_Xbar h4 Y (xz_mem_Xbar_of_two_zeros h4 hjv hkv ht hj1 hj2)
  rw [hYj] at h1
  have hu : mat Y *ᵥ v = mat (Y * colProd r v) *ᵥ Pi.single r 1 := by
    rw [mat_mul, ← Matrix.mulVec_mulVec, hz]
  have hjM : j ᵥ* mat Y = j := by
    calc j ᵥ* mat Y = (j ᵥ* matInv Y) ᵥ* mat Y := by rw [hYj]
      _ = j := by rw [Matrix.vecMul_vecMul, matInv_mul_mat, Matrix.vecMul_one]
  have hju : j ⬝ᵥ (mat Y *ᵥ v) = 0 := by rw [Matrix.dotProduct_mulVec, hjM, hjv]
  have hku : (Pi.single r (1 : A) ᵥ* matInv (Y * colProd r v)) ⬝ᵥ (mat Y *ᵥ v) = 1 := by
    rw [hu]
    exact unimod_col _ r
  have h2 := xz_mem_Xbar_of_two_zeros h4 hju hku ht hj1 hj2
  have hsub := Xbar_subsingleton h4 (Y * colProd r v) r j
  rw [← hu] at hsub
  exact hsub h1 h2

/-- **vdK 3.19, the case without a common zero.** If `j i = 0`, `j` has two zeros,
`j π(Y)⁻¹ = j` and `π(Y) i = i`, then `Y` commutes with `x(i, j)`. -/
theorem conj_xz_of_two_zeros (h4 : 4 ≤ Fintype.card I) {i j : I → A} (hji : j ⬝ᵥ i = 0)
    {t1 t2 : I} (ht : t1 ≠ t2) (hj1 : j t1 = 0) (hj2 : j t2 = 0) (Y : SteinbergGroup I A)
    (hYj : j ᵥ* matInv Y = j) (hYi : mat Y *ᵥ i = i) : Y * xz i j * Y⁻¹ = xz i j := by
  obtain ⟨va, hva⟩ : ∃ va : I → A, va = Pi.single t1 1 + Pi.single t2 (i t2 - 1) := ⟨_, rfl⟩
  have hva1 : va t1 = 1 := by
    rw [hva, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne ht, add_zero]
  have hvb2 : (i - va) t2 = 1 := by
    rw [Pi.sub_apply, hva, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne ht.symm, zero_add,
      sub_sub_cancel]
  have hjva : j ⬝ᵥ va = 0 := by
    rw [hva, dotProduct_add, dotProduct_single, dotProduct_single, hj1, hj2, zero_mul, zero_mul,
      add_zero]
  have hjvb : j ⬝ᵥ (i - va) = 0 := by rw [dotProduct_sub, hji, hjva, sub_zero]
  have hjM : j ᵥ* mat Y = j := by
    calc j ᵥ* mat Y = (j ᵥ* matInv Y) ᵥ* mat Y := by rw [hYj]
      _ = j := by rw [Matrix.vecMul_vecMul, matInv_mul_mat, Matrix.vecMul_one]
  have hjMa : j ⬝ᵥ (mat Y *ᵥ va) = 0 := by rw [Matrix.dotProduct_mulVec, hjM, hjva]
  have hjMb : j ⬝ᵥ (mat Y *ᵥ (i - va)) = 0 := by rw [Matrix.dotProduct_mulVec, hjM, hjvb]
  have hsplit : xz i j = xz va j * xz (i - va) j := by
    rw [xz_add_col ht hjva hjvb hj1 hj2, add_sub_cancel]
  calc Y * xz i j * Y⁻¹ = (Y * xz va j * Y⁻¹) * (Y * xz (i - va) j * Y⁻¹) := by
        rw [hsplit]
        group
    _ = xz i j := by
        rw [conj_xz_col h4 hva1 hjva ht hj1 hj2 Y hYj, conj_xz_col h4 hvb2 hjvb ht hj1 hj2 Y hYj,
          xz_add_col ht hjMa hjMb hj1 hj2, ← Matrix.mulVec_add, add_sub_cancel, hYi]

#audit_axioms conj_xz_of_two_zeros

/-- **vdK 3.19.** If `j i = k i = 0` and `j`, `k` each have at most two nonzero coordinates, then
`x(i, j)` and `x(i, k)` commute. -/
theorem xz_commute (h4 : 4 ≤ Fintype.card I) {i j k : I → A} (hji : j ⬝ᵥ i = 0)
    (hki : k ⬝ᵥ i = 0) {p1 q1 p2 q2 : I} (hj : ∀ t, t ≠ p1 → t ≠ q1 → j t = 0)
    (hk : ∀ t, t ≠ p2 → t ≠ q2 → k t = 0) : Commute (xz i j) (xz i k) := by
  by_cases hc : ∃ c, c ≠ p1 ∧ c ≠ q1 ∧ c ≠ p2 ∧ c ≠ q2
  · obtain ⟨c, h1, h2, h3, h4'⟩ := hc
    obtain ⟨r, hrp, hrq, hrc⟩ := exists_ne_three h4 p1 q1 c
    obtain ⟨q, hqp, hqq, hqc⟩ := exists_ne_three h4 p2 q2 c
    have e1 := xz_add (p := c) (q := q) (r := r) hrc hqc hji hki (hj c h1 h2) (hj r hrp hrq)
      (hk c h3 h4') (hk q hqp hqq)
    have e2 := xz_add (p := c) (q := r) (r := q) hqc hrc hki hji (hk c h3 h4') (hk q hqp hqq)
      (hj c h1 h2) (hj r hrp hrq)
    show xz i j * xz i k = xz i k * xz i j
    rw [e1, e2, add_comm]
  · push_neg at hc
    obtain ⟨t, htp1, htq1, htp2⟩ := exists_ne_three h4 p1 q1 p2
    have htq2 : t = q2 := hc t htp1 htq1 htp2
    have hq2p1 : q2 ≠ p1 := htq2 ▸ htp1
    have hq2q1 : q2 ≠ q1 := htq2 ▸ htq1
    obtain ⟨t', htp1', htq1', htq2'⟩ := exists_ne_three h4 p1 q1 q2
    have htp2' : t' = p2 := by
      by_contra hne
      exact htq2' (hc t' htp1' htq1' hne)
    have hp2p1 : p2 ≠ p1 := htp2' ▸ htp1'
    have hp2q1 : p2 ≠ q1 := htp2' ▸ htq1'
    have hp2q2 : p2 ≠ q2 := htp2' ▸ htq2'
    have hkp1 : k p1 = 0 := hk p1 (Ne.symm hp2p1) (Ne.symm hq2p1)
    have hst := stU_xz hki hkp1
    have hYj : j ᵥ* matInv (xz i k) = j := by
      rw [matInv_eq_of_stU hst, vecMul_one_sub_vecMulVec, hji, zero_smul, sub_zero]
    have hYi : mat (xz i k) *ᵥ i = i := by
      rw [mat_eq_of_stU hst, one_add_vecMulVec_mulVec, hki, zero_smul, add_zero]
    have hC := conj_xz_of_two_zeros h4 hji hp2q2 (hj p2 hp2p1 hp2q1) (hj q2 hq2p1 hq2q1)
      (xz i k) hYj hYi
    exact (mul_inv_eq_iff_eq_mul.mp hC).symm

#audit_axioms xz_commute

/-! ### vdK 3.20: `x_i(j; k)` -/

theorem piece_commute (h4 : 4 ≤ Fintype.card I) (i j j' k : I → A) (x y : I × I) :
    Commute (xz i (piece i j k x)) (xz i (piece i j' k y)) :=
  xz_commute (p1 := x.1) (q1 := x.2) (p2 := y.1) (q2 := y.2) h4
    (vdkPiece_dotProduct i j k x.1 x.2) (vdkPiece_dotProduct i j' k y.1 y.2)
    (fun _ h1 h2 => vdkPiece_apply_of_ne i j k h1 h2)
    (fun _ h1 h2 => vdkPiece_apply_of_ne i j' k h1 h2)

/-- **vdK 3.20.** `x_i(j; k)`: the product of all `x(i, w_pq)`; by 3.19 the order does not
matter. -/
noncomputable def xk (h4 : 4 ≤ Fintype.card I) (i j k : I → A) : SteinbergGroup I A :=
  (Finset.univ : Finset (I × I)).noncommProd (fun x => xz i (piece i j k x))
    (fun x _ y _ _ => piece_commute h4 i j j k x y)

theorem xk_eq_list_prod (h4 : 4 ≤ Fintype.card I) (i j k : I → A) {L : List (I × I)}
    (hnd : L.Nodup) (hL : L.toFinset = Finset.univ) :
    xk h4 i j k = (L.map fun x => xz i (piece i j k x)).prod := by
  rw [xk, Finset.noncommProd_congr (f := fun x => xz i (piece i j k x))
    (g := fun x => xz i (piece i j k x)) hL.symm (fun _ _ => rfl),
    Finset.noncommProd_toFinset _ _ _ hnd]

/-- **vdK 3.18 with 3.19.** `x(i, j) = x_i(j; k)` when `j` has two zeros. -/
theorem xz_eq_xk (h4 : 4 ≤ Fintype.card I) {i j k : I → A} (hji : j ⬝ᵥ i = 0)
    (hk : k ⬝ᵥ i = 1) {a b : I} (hab : a ≠ b) (hja : j a = 0) (hjb : j b = 0) :
    xz i j = xk h4 i j k := by
  rw [xk_eq_list_prod h4 i j k (nodup_pairsAll hab) (toFinset_pairsAll a b),
    xz_eq_prod_pairsAll h4 hji hk hab hja hjb]

theorem vdkPiece_add (i u v k : I → A) (p q : I) :
    vdkPiece i (u + v) k p q = vdkPiece i u k p q + vdkPiece i v k p q := by
  rw [vdkPiece, vdkPiece, vdkPiece, Pi.add_apply, add_mul, add_smul]

/-- **vdK 3.20.** `x_i(u; k) x_i(v; k) = x_i(u + v; k)`. -/
theorem xk_add (h4 : 4 ≤ Fintype.card I) (i u v k : I → A) :
    xk h4 i u k * xk h4 i v k = xk h4 i (u + v) k := by
  have hpt : ∀ x : I × I,
      xz i (piece i u k x) * xz i (piece i v k x) = xz i (piece i (u + v) k x) := by
    rintro ⟨p, q⟩
    obtain ⟨c, c', hcc, hcp, hcq, hc'p, hc'q⟩ := exists_two_ne_of_card h4 p q
    show xz i (vdkPiece i u k p q) * xz i (vdkPiece i v k p q) = xz i (vdkPiece i (u + v) k p q)
    rw [vdkPiece_add]
    exact xz_add (p := c) (q := c') (r := c') (Ne.symm hcc) (Ne.symm hcc)
      (vdkPiece_dotProduct i u k p q) (vdkPiece_dotProduct i v k p q)
      (vdkPiece_apply_of_ne i u k hcp hcq) (vdkPiece_apply_of_ne i u k hc'p hc'q)
      (vdkPiece_apply_of_ne i v k hcp hcq) (vdkPiece_apply_of_ne i v k hc'p hc'q)
  rw [xk, xk, ← Finset.noncommProd_mul_distrib (fun x => xz i (piece i u k x))
    (fun x => xz i (piece i v k x)) _ _ (fun x _ y _ _ => piece_commute h4 i v u k x y), xk]
  exact Finset.noncommProd_congr rfl (fun x _ => hpt x) _

theorem xk_zero (h4 : 4 ≤ Fintype.card I) (i k : I → A) : xk h4 i 0 k = 1 := by
  unfold xk
  refine (Finset.noncommProd_eq_pow_card _ _ _ 1 fun x _ => ?_).trans (one_pow _)
  show xz i (vdkPiece i 0 k x.1 x.2) = 1
  rw [vdkPiece_of_apply_eq_zero (Pi.zero_apply x.1) x.2, xz_zero]

theorem xk_mem_Xbar (h4 : 4 ≤ Fintype.card I) {i j k : I → A} (hji : j ⬝ᵥ i = 0)
    (hk : k ⬝ᵥ i = 1) : xk h4 i j k ∈ Xbar i j := by
  obtain ⟨e⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨a, b, hab, -, -, -, -⟩ := exists_two_ne_of_card h4 e e
  refine mem_Xbar.2 ⟨(pairsAll a b).map (piece i j k), ?_, sum_pairsAll hji hk hab, ?_⟩
  · intro w hw
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hw
    exact piece_isBasic i j k x
  · rw [map_map_xz, xk_eq_list_prod h4 i j k (nodup_pairsAll hab) (toFinset_pairsAll a b)]

/-! ### vdK 3.21 -/

/-- **vdK 3.21.** If `k i = 1`, every element of `X̄(i, j)` is `x_i(j; k)`. -/
theorem eq_xk_of_mem_Xbar (h4 : 4 ≤ Fintype.card I) {i j k : I → A} (hk : k ⬝ᵥ i = 1)
    {g : SteinbergGroup I A} (hg : g ∈ Xbar i j) : g = xk h4 i j k := by
  obtain ⟨L, hL, rfl, rfl⟩ := hg
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, List.sum_nil, xk_zero]
  | cons w L ih =>
    have hw : IsBasic i w := hL w (List.mem_cons.2 (Or.inl rfl))
    obtain ⟨a, b, hab, hwa, hwb⟩ := hw.exists_two_zeros h4
    rw [List.map_cons, List.prod_cons, List.sum_cons, ← xk_add,
      ih (fun w' h' => hL w' (List.mem_cons.2 (Or.inr h'))),
      xz_eq_xk h4 hw.dotProduct hk hab hwa hwb]

#audit_axioms eq_xk_of_mem_Xbar

/-! ### vdK 3.22: the elements `X(i, j)` and Theorem 1 -/

/-- A row `k` with `k i = 1`, chosen for each unimodular column `i`. -/
noncomputable def unitRow {i : I → A} (hi : IsUnimodular i) : I → A :=
  Classical.choose hi

theorem unitRow_spec {i : I → A} (hi : IsUnimodular i) : unitRow hi ⬝ᵥ i = 1 :=
  Classical.choose_spec hi

/-- `X(i, j) = x_i(j; k)` for `(i, j) ∈ U`, with the chosen `k`. -/
noncomputable def eltOf (h4 : 4 ≤ Fintype.card I) (p : (I → A) × (I → A)) (hp : p ∈ U I A) :
    SteinbergGroup I A :=
  xk h4 p.1 p.2 (unitRow (mem_U.1 hp).1)

theorem eltOf_mem_Xbar (h4 : 4 ≤ Fintype.card I) (p : (I → A) × (I → A)) (hp : p ∈ U I A) :
    eltOf h4 p hp ∈ Xbar p.1 p.2 :=
  xk_mem_Xbar h4 (mem_U.1 hp).2 (unitRow_spec _)

theorem eq_eltOf_of_mem_Xbar (h4 : 4 ≤ Fintype.card I) (p : (I → A) × (I → A))
    (hp : p ∈ U I A) {g : SteinbergGroup I A} (hg : g ∈ Xbar p.1 p.2) : g = eltOf h4 p hp :=
  eq_xk_of_mem_Xbar h4 (unitRow_spec _) hg

theorem stU_eltOf (h4 : 4 ≤ Fintype.card I) (p : (I → A) × (I → A)) (hp : p ∈ U I A) :
    stU I A (eltOf h4 p hp) = eUnit p.1 p.2 (mem_U.1 hp).2 :=
  stU_of_mem_Xbar h4 (eltOf_mem_Xbar h4 p hp) _

variable (I A) in
/-- **vdK 3.22.** The elements `X(i, j)` satisfy vdK's requirements 3.6. -/
noncomputable def elements (h4 : 4 ≤ Fintype.card I) : Elements I A where
  elt := eltOf h4
  mul i j k _ _ _ := xk_add h4 i j k _
  conj p q hp hq := by
    have hmem := conj_mem_Xbar h4 (eltOf h4 p hp) (eltOf_mem_Xbar h4 q hq)
    have hst := stU_eltOf h4 p hp
    rw [mat_eq_of_stU hst, matInv_eq_of_stU hst, one_add_vecMulVec_mulVec,
      vecMul_one_sub_vecMulVec] at hmem
    exact eq_eltOf_of_mem_Xbar h4 (conjPair p q) (conjPair_mem hp hq) hmem
  std p q hpq a := by
    have hz : (Pi.single q a : I → A) p = 0 := Pi.single_eq_of_ne hpq a
    have hdot : (Pi.single q a : I → A) ⬝ᵥ Pi.single p 1 = 0 := by
      rw [dotProduct_single, hz, zero_mul]
    have hone : Pi.single p (1 : A) ⬝ᵥ Pi.single p 1 = 1 := by
      rw [dotProduct_single, Pi.single_eq_same, mul_one]
    obtain ⟨r, s, hrs, hrq, -, hsq, -⟩ := exists_two_ne_of_card h4 q q
    have hmem := xz_mem_Xbar_of_two_zeros h4 hdot hone hrs (Pi.single_eq_of_ne hrq a)
      (Pi.single_eq_of_ne hsq a)
    rw [xz_eq hdot hz, xvw_std p q hpq a] at hmem
    exact (eq_eltOf_of_mem_Xbar h4 (stdPair p q a) (stdPair_mem hpq a) hmem).symm
  proj p hp := stU_eltOf h4 p hp

/-- **vdK's Theorem 1.** For `n ≥ 4`, `φ : St(n, A) → St*(n, A)` is an isomorphism. -/
theorem theorem1 (h4 : 4 ≤ Fintype.card I) : Theorem1At I A :=
  theorem1_of_elements h4 (elements I A h4)

#audit_axioms theorem1

/-- For `w` with two zeros `r ≠ s`, `X(v, w)` is the elementary `x(v, w)` of vdK 3.10, computed
at `r`. -/
theorem elements_elt_eq_xvw (h4 : 4 ≤ Fintype.card I) {v w : I → A} (h : (v, w) ∈ U I A)
    {r s : I} (hrs : r ≠ s) (hwr : w r = 0) (hws : w s = 0) :
    (elements I A h4).elt (v, w) h = xvw v w r := by
  have hwv : w ⬝ᵥ v = 0 := (mem_U.1 h).2
  have hv : IsUnimodular v := (mem_U.1 h).1
  show eltOf h4 (v, w) h = xvw v w r
  rw [← xz_eq hwv hwr]
  exact (xz_eq_xk h4 hwv (unitRow_spec hv) hrs hwr hws).symm

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation
