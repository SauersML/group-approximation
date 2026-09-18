import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegWeyl
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellTorus
import GroupApproximation.Meta.AxiomGuard

/-!
# Degree reduction for `K₂(F_p[X])`, part 2: the parabolic `P(F_p[X])` in `St_I(F_p[X])`

Lane `bh-met-91c`.  Put `R = F_p[X]`, fix a finset `K`, an index `L ∉ K`, an index `m ∈ K` and a
third index `n ∉ {m, L}`, and write `K' = K ∪ {L}`.  Inside `St_I(R)`:

* `k2PolyDeg_S`: `S = ⟨x_ij(f) : i, j ∈ K⟩` (the Levi block);
* `k2PolyDeg_V`: `V = ⟨x_Lj(f) : j ∈ K⟩` (the unipotent radical, row `L`);
* `k2PolyDeg_torus`: `c ↦ C(h_mL(c))`, a homomorphism `F_pˣ → St_I(R)` because symbols vanish
  over `F_p` (`FieldK2.bruhatBigCell_h_mul_zmod`);
* `k2PolyDeg_P = T ⊔ (S ⊔ V)` with `T` the range of the torus (the parabolic `P(R)`);
* `k2PolyDeg_A = C(G_{K'}(F_p))` (the constants) and `k2PolyDeg_G = G_{K'}(R)`.

Proved here: `S` normalizes `V`, the torus normalizes every root span, and hence every element of
`P` is `t · s · v` with `t` in the torus, `s ∈ S` and `v ∈ V` (`k2PolyDeg_P_decomp`).

Truth check (paper).  For `i, j ∈ K` and `l ∈ K`: `x_ij(a)` commutes with `x_Ll(b)` unless
`l = i`, and `x_ij(a) x_Li(b) x_ij(a)⁻¹ = x_Li(b) x_Lj(-ba)` (C2).  The torus preserves each
root group (`k2PolyDeg_h_conj_exists`).  With `S ≤ N(V)` and `T ≤ N(S ⊔ V)`, Mathlib's
`coe_mul_of_left_le_normalizer_right` gives `S ⊔ V = S V` and `T ⊔ (S ⊔ V) = T (S ⊔ V)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h x_congr conj_of_commute
  conj_x_right)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  x_mem_rootSpan rootSpan_conj_mem rootSpan_normalizes)

section Normalizer

variable {G : Type*} [Group G]

/-- A subgroup that conjugates `N` into itself lies in the normalizer of `N`. -/
theorem k2PolyDeg_le_normalizer {H N : Subgroup G}
    (hc : ∀ s ∈ H, ∀ v ∈ N, s * v * s⁻¹ ∈ N) : H ≤ N.normalizer := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨hc s hs v, fun hv => ?_⟩
  have hw := hc s⁻¹ (H.inv_mem hs) _ hv
  rwa [inv_inv, show s⁻¹ * (s * v * s⁻¹) * s = v by group] at hw

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_le_normalizer

end Normalizer

variable {I : Type} [Fintype I] [DecidableEq I]

section Defs

variable (p : ℕ) [Fact p.Prime]

/-- `S = ⟨x_ij(f) : i, j ∈ K⟩ ≤ St_I(F_p[X])`. -/
def k2PolyDeg_S (K : Finset I) : Subgroup (SteinbergGroup I (Polynomial (ZMod p))) :=
  rootSpan (R := Polynomial (ZMod p)) fun i j => i ∈ K ∧ j ∈ K

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_S

/-- `V = ⟨x_Lj(f) : j ∈ K⟩ ≤ St_I(F_p[X])`. -/
def k2PolyDeg_V (K : Finset I) (L : I) : Subgroup (SteinbergGroup I (Polynomial (ZMod p))) :=
  rootSpan (R := Polynomial (ZMod p)) fun i j => i = L ∧ j ∈ K

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_V

/-- `G_{K'}(F_p[X])`, `K' = K ∪ {L}`. -/
def k2PolyDeg_G (K : Finset I) (L : I) : Subgroup (SteinbergGroup I (Polynomial (ZMod p))) :=
  rootSpan (R := Polynomial (ZMod p)) fun i j => i ∈ insert L K ∧ j ∈ insert L K

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_G

/-- The constants `C(G_{K'}(F_p)) ≤ St_I(F_p[X])`. -/
def k2PolyDeg_A (K : Finset I) (L : I) : Subgroup (SteinbergGroup I (Polynomial (ZMod p))) :=
  (rootSpan (R := ZMod p) fun i j => i ∈ insert L K ∧ j ∈ insert L K).map
    (ringMap (Polynomial.C : ZMod p →+* Polynomial (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_A

/-- The torus `c ↦ C(h_mL(c))`; multiplicative because symbols vanish over `F_p`. -/
def k2PolyDeg_torus (m L n : I) (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) :
    (ZMod p)ˣ →* SteinbergGroup I (Polynomial (ZMod p)) :=
  (ringMap (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).comp
    (MonoidHom.mk' (fun c : (ZMod p)ˣ => h m L hmL c) fun c c' => by
      show h m L hmL (c * c') = h m L hmL c * h m L hmL c'
      rw [FieldK2.bruhatBigCell_h_mul_zmod m L n hmL hmn hLn c c', mul_comm c' c])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_torus

/-- The parabolic `P = T ⊔ (S ⊔ V)`. -/
def k2PolyDeg_P (K : Finset I) (m L n : I) (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) :
    Subgroup (SteinbergGroup I (Polynomial (ZMod p))) :=
  (k2PolyDeg_torus p m L n hmL hmn hLn).range ⊔ (k2PolyDeg_S p K ⊔ k2PolyDeg_V p K L)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_P

end Defs

variable {p : ℕ} [Fact p.Prime]

/-- The torus in closed form: `C(h_mL(c)) = h_mL(C c)`. -/
theorem k2PolyDeg_torus_apply (m L n : I) (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)
    (c : (ZMod p)ˣ) :
    k2PolyDeg_torus p m L n hmL hmn hLn c =
      h m L hmL (Units.map (Polynomial.C : ZMod p →+* Polynomial (ZMod p)).toMonoidHom c) := by
  show ringMap (Polynomial.C : ZMod p →+* Polynomial (ZMod p)) (h m L hmL c) = _
  exact k2PolyDeg_ringMap_h _ m L hmL c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_torus_apply

/-- The torus conjugates every root span into itself. -/
theorem k2PolyDeg_torus_conj_rootSpan (m L n : I) (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)
    (q : I → I → Prop) (c : (ZMod p)ˣ) {g : SteinbergGroup I (Polynomial (ZMod p))}
    (hg : g ∈ rootSpan (R := Polynomial (ZMod p)) q) :
    k2PolyDeg_torus p m L n hmL hmn hLn c * g * (k2PolyDeg_torus p m L n hmL hmn hLn c)⁻¹ ∈
      rootSpan (R := Polynomial (ZMod p)) q := by
  rw [k2PolyDeg_torus_apply]
  refine rootSpan_conj_mem (fun k l hkl b hq => ?_) hg
  obtain ⟨b', hb'⟩ := k2PolyDeg_h_conj_exists m L k l hmL hkl ⟨n, hmn, hLn⟩
    (Units.map (Polynomial.C : ZMod p →+* Polynomial (ZMod p)).toMonoidHom c) b
  rw [hb']
  exact x_mem_rootSpan hkl b' hq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_torus_conj_rootSpan

/-- `S` normalizes `V`. -/
theorem k2PolyDeg_S_le_normalizer_V {K : Finset I} {L : I} (hLK : L ∉ K) :
    k2PolyDeg_S p K ≤ (k2PolyDeg_V p K L).normalizer := by
  refine k2PolyDeg_le_normalizer fun s hs v hv => rootSpan_normalizes ?_ hs hv
  intro i j hij a hp k l hkl b hq
  obtain ⟨hi, hj⟩ := hp
  obtain ⟨hk, hl⟩ := hq
  have hiL : i ≠ L := fun e => hLK (e ▸ hi)
  have hjL : j ≠ L := fun e => hLK (e ▸ hj)
  by_cases hli : l = i
  · have e : x k l hkl b = x L i hiL.symm b := x_congr _ _ hk hli rfl
    rw [e, conj_x_right L i j hiL.symm hij hjL.symm b a]
    exact Subgroup.mul_mem _ (x_mem_rootSpan _ _ ⟨rfl, hi⟩) (x_mem_rootSpan _ _ ⟨rfl, hj⟩)
  · have hjk : j ≠ k := fun e => hjL (e.trans hk)
    rw [conj_of_commute (x_commute_of_ne i j k l hij hkl hjk hli a b)]
    exact x_mem_rootSpan hkl b ⟨hk, hl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_S_le_normalizer_V

/-- Every element of `S ⊔ V` is `s v` with `s ∈ S`, `v ∈ V`. -/
theorem k2PolyDeg_SV_decomp {K : Finset I} {L : I} (hLK : L ∉ K)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyDeg_S p K ⊔ k2PolyDeg_V p K L) :
    ∃ s ∈ k2PolyDeg_S p K, ∃ v ∈ k2PolyDeg_V p K L, s * v = g := by
  have hg' : g ∈ (k2PolyDeg_S p K : Set (SteinbergGroup I (Polynomial (ZMod p)))) *
      (k2PolyDeg_V p K L : Set (SteinbergGroup I (Polynomial (ZMod p)))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (k2PolyDeg_S_le_normalizer_V hLK)]
    exact hg
  exact hg'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_SV_decomp

end GroupApproximation.BooneHigman.Metabelian.ElemFP
