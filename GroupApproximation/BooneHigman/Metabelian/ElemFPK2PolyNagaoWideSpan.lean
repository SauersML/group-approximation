import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylMain
import GroupApproximation.Meta.AxiomGuard

/-!
# The wide Nagao step, part 1: root spans around `Q`

Lane `bh-met-93l`.  Notation of `ElemFPK2PolyEuclidGen`; `R = F_p[X]`, `m ∈ K`, `L ∉ K`.

* `k2PolyNagaoWide_Qr K L = ⟨x_ij(f) : i ∈ K ∪ {L}, j ∈ K⟩`, equal to `Q = S ⊔ V`
  (`k2PolyNagaoWide_Q_le_Qr`, `k2PolyNagaoWide_Qr_le_Q`).
* `k2PolyNagaoWide_Qm K m L = ⟨x_ij(f) : i ∈ K ∪ {L}, j ∈ K \ {m}⟩ ≤ Q`.
* `k2PolyNagaoWide_Gml m L = ⟨x_mL(f), x_Lm(f)⟩`, containing every Euclidean word
  `k2PolyNagaoSigma_pair` (`k2PolyNagaoWide_pair_mem`), and normalising `Q^m`
  (`k2PolyNagaoWide_Gml_conj_Qm`: `x_ab x_bl x_ab⁻¹ = x_al x_bl`, the rest commute).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h x_congr conj_x_left
  conj_of_commute)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  x_mem_rootSpan rootSpan_induction rootSpan_mono rootSpan_normalizes)

variable {I : Type} [Fintype I] [DecidableEq I]

section Defs

variable (p : ℕ) [Fact p.Prime]

/-- `Q` as one root span: `⟨x_ij(f) : i ∈ K ∪ {L}, j ∈ K⟩`. -/
def k2PolyNagaoWide_Qr (K : Finset I) (L : I) :
    Subgroup (SteinbergGroup I (Polynomial (ZMod p))) :=
  rootSpan (R := Polynomial (ZMod p)) fun i j => i ∈ insert L K ∧ j ∈ K

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Qr

/-- `Q^m = ⟨x_ij(f) : i ∈ K ∪ {L}, j ∈ K \ {m}⟩`. -/
def k2PolyNagaoWide_Qm (K : Finset I) (m L : I) :
    Subgroup (SteinbergGroup I (Polynomial (ZMod p))) :=
  rootSpan (R := Polynomial (ZMod p)) fun i j => i ∈ insert L K ∧ j ∈ K.erase m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Qm

/-- `G_{mL} = ⟨x_mL(f), x_Lm(f)⟩`. -/
def k2PolyNagaoWide_Gml (m L : I) : Subgroup (SteinbergGroup I (Polynomial (ZMod p))) :=
  rootSpan (R := Polynomial (ZMod p)) fun i j => (i = m ∨ i = L) ∧ (j = m ∨ j = L)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Gml

end Defs

variable {p : ℕ} [Fact p.Prime]

/-- `Q ≤ Q_r`. -/
theorem k2PolyNagaoWide_Q_le_Qr (K : Finset I) (L : I) :
    k2PolyNF_Q p K L ≤ k2PolyNagaoWide_Qr p K L := by
  show k2PolyDeg_S p K ⊔ k2PolyDeg_V p K L ≤ k2PolyNagaoWide_Qr p K L
  refine sup_le (fun _ hg => ?_) (fun _ hg => ?_)
  · exact rootSpan_mono (p := fun i j => i ∈ K ∧ j ∈ K)
      (q := fun i j => i ∈ insert L K ∧ j ∈ K)
      (fun _ _ _ hij => ⟨Finset.mem_insert_of_mem hij.1, hij.2⟩) hg
  · exact rootSpan_mono (p := fun i j => i = L ∧ j ∈ K)
      (q := fun i j => i ∈ insert L K ∧ j ∈ K)
      (fun _ _ _ hij => ⟨Finset.mem_insert.2 (Or.inl hij.1), hij.2⟩) hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Q_le_Qr

/-- `Q_r ≤ Q`. -/
theorem k2PolyNagaoWide_Qr_le_Q (K : Finset I) (L : I) :
    k2PolyNagaoWide_Qr p K L ≤ k2PolyNF_Q p K L := by
  intro _ hg
  refine rootSpan_induction (p := fun i j => i ∈ insert L K ∧ j ∈ K)
    (Q := fun g => g ∈ k2PolyNF_Q p K L) ?_ (Subgroup.one_mem _)
    (fun _ _ _ _ h1 h2 => Subgroup.mul_mem _ h1 h2) hg
  intro i j hij a hq
  have hq' : i ∈ insert L K ∧ j ∈ K := hq
  show x i j hij a ∈ k2PolyDeg_S p K ⊔ k2PolyDeg_V p K L
  rcases Finset.mem_insert.1 hq'.1 with hiL | hiK
  · exact Subgroup.mem_sup_right
      (x_mem_rootSpan (p := fun i j => i = L ∧ j ∈ K) hij a ⟨hiL, hq'.2⟩)
  · exact Subgroup.mem_sup_left
      (x_mem_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) hij a ⟨hiK, hq'.2⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Qr_le_Q

/-- `Q^m ≤ Q`. -/
theorem k2PolyNagaoWide_Qm_le_Q (K : Finset I) (m L : I) :
    k2PolyNagaoWide_Qm p K m L ≤ k2PolyNF_Q p K L := fun _ hg =>
  k2PolyNagaoWide_Qr_le_Q K L <| rootSpan_mono (p := fun i j => i ∈ insert L K ∧ j ∈ K.erase m)
    (q := fun i j => i ∈ insert L K ∧ j ∈ K)
    (fun _ _ _ hij => ⟨hij.1, Finset.mem_of_mem_erase hij.2⟩) hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Qm_le_Q

variable {m L : I} (hmL : m ≠ L)

/-- The roots `x_ij(f)`, `i, j ∈ {m, L}`, lie in `G_{mL}`. -/
theorem k2PolyNagaoWide_x_mem_Gml {i j : I} (hij : i ≠ j) (hi : i = m ∨ i = L)
    (hj : j = m ∨ j = L) (a : Polynomial (ZMod p)) :
    x i j hij a ∈ k2PolyNagaoWide_Gml p m L :=
  x_mem_rootSpan (p := fun i j => (i = m ∨ i = L) ∧ (j = m ∨ j = L)) hij a ⟨hi, hj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_x_mem_Gml

/-- `w_mL(u) ∈ G_{mL}`. -/
theorem k2PolyNagaoWide_w_mem (u : (Polynomial (ZMod p))ˣ) :
    w m L hmL u ∈ k2PolyNagaoWide_Gml p m L := by
  rw [w]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (k2PolyNagaoWide_x_mem_Gml hmL (Or.inl rfl) (Or.inr rfl) _)
      (k2PolyNagaoWide_x_mem_Gml hmL.symm (Or.inr rfl) (Or.inl rfl) _))
    (k2PolyNagaoWide_x_mem_Gml hmL (Or.inl rfl) (Or.inr rfl) _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_w_mem

/-- `h_mL(u) ∈ G_{mL}`. -/
theorem k2PolyNagaoWide_h_mem (u : (Polynomial (ZMod p))ˣ) :
    h m L hmL u ∈ k2PolyNagaoWide_Gml p m L := by
  show w m L hmL u * w m L hmL (-1) ∈ k2PolyNagaoWide_Gml p m L
  exact Subgroup.mul_mem _ (k2PolyNagaoWide_w_mem hmL u) (k2PolyNagaoWide_w_mem hmL (-1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_h_mem

/-- `τ(b) ∈ G_{mL}`. -/
theorem k2PolyNagaoWide_tau_mem (b : Polynomial (ZMod p)) :
    k2PolyNagaoSigma_tau p m L hmL b ∈ k2PolyNagaoWide_Gml p m L := by
  unfold k2PolyNagaoSigma_tau
  split_ifs
  · exact Subgroup.one_mem _
  · exact Subgroup.inv_mem _ (k2PolyNagaoWide_h_mem hmL _)
  · exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_tau_mem
/-- Every Euclidean word `pair a b` lies in `G_{mL}` (well-founded induction on `deg a`). -/
theorem k2PolyNagaoWide_pair_mem (a : Polynomial (ZMod p)) :
    ∀ b, k2PolyNagaoSigma_pair p m L hmL a b ∈ k2PolyNagaoWide_Gml p m L := by
  induction a using (Polynomial.degree_lt_wf (R := ZMod p)).induction with
  | _ a ih =>
    intro b
    by_cases ha : a = 0
    · rw [ha, k2PolyNagaoSigma_pair_zero]
      exact k2PolyNagaoWide_tau_mem hmL b
    · rw [k2PolyNagaoSigma_pair_of_ne p m L hmL ha]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (k2PolyNagaoWide_x_mem_Gml hmL.symm (Or.inr rfl) (Or.inl rfl) _)
          (k2PolyNagaoWide_w_mem hmL _))
        (ih _ (Polynomial.degree_mod_lt b ha) _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_pair_mem

/-- `σ₀(v) = pair (v m) (v L) ∈ G_{mL}`. -/
theorem k2PolyNagaoWide_sigma0_mem (v : I → Polynomial (ZMod p)) :
    k2PolyNagaoSigma_sigma p m L hmL v ∈ k2PolyNagaoWide_Gml p m L := by
  show k2PolyNagaoSigma_pair p m L hmL (v m) (v L) ∈ k2PolyNagaoWide_Gml p m L
  exact k2PolyNagaoWide_pair_mem hmL (v m) (v L)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_sigma0_mem

/-- `G_{mL}` normalises `Q^m`: for `a, b ∈ {m, L}`, `k ∈ K ∪ {L}`, `l ∈ K \ {m}`, the
conjugate `x_ab(c) x_kl(d) x_ab(c)⁻¹` is `x_al(cd) x_bl(d)` when `b = k`, else `x_kl(d)`. -/
theorem k2PolyNagaoWide_Gml_conj_Qm {K : Finset I} (hmK : m ∈ K) (hLK : L ∉ K)
    {s : SteinbergGroup I (Polynomial (ZMod p))} (hs : s ∈ k2PolyNagaoWide_Gml p m L)
    {u : SteinbergGroup I (Polynomial (ZMod p))} (hu : u ∈ k2PolyNagaoWide_Qm p K m L) :
    s * u * s⁻¹ ∈ k2PolyNagaoWide_Qm p K m L := by
  refine rootSpan_normalizes (p := fun i j => (i = m ∨ i = L) ∧ (j = m ∨ j = L))
    (q := fun i j => i ∈ insert L K ∧ j ∈ K.erase m) ?_ hs hu
  intro a b hab c hp k l hkl d hq
  have hp' : (a = m ∨ a = L) ∧ (b = m ∨ b = L) := hp
  have hq' : k ∈ insert L K ∧ l ∈ K.erase m := hq
  have hlm : l ≠ m := Finset.ne_of_mem_erase hq'.2
  have hlL : l ≠ L := fun e => hLK (by rw [← e]; exact Finset.mem_of_mem_erase hq'.2)
  have hal : a ≠ l := by
    rcases hp'.1 with e | e
    · exact fun e' => hlm (e'.symm.trans e)
    · exact fun e' => hlL (e'.symm.trans e)
  have haK : a ∈ insert L K := by
    rcases hp'.1 with e | e
    · exact Finset.mem_insert_of_mem (by rw [e]; exact hmK)
    · exact Finset.mem_insert.2 (Or.inl e)
  by_cases hbk : b = k
  · have hbl : b ≠ l := fun e => hkl (hbk.symm.trans e)
    have hbK : b ∈ insert L K := by rw [hbk]; exact hq'.1
    rw [x_congr hkl hbl hbk.symm rfl (rfl : d = d), conj_x_left a b l hab hbl hal c d]
    exact Subgroup.mul_mem _
      (x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ K.erase m) hal _ ⟨haK, hq'.2⟩)
      (x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ K.erase m) hbl _ ⟨hbK, hq'.2⟩)
  · rw [conj_of_commute (x_commute_of_ne a b k l hab hkl hbk (Ne.symm hal) c d)]
    exact x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ K.erase m) hkl d hq'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Gml_conj_Qm

end GroupApproximation.BooneHigman.Metabelian.ElemFP
