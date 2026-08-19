import GroupApproximation.Analysis.CollapsePrintedContradiction
import GroupApproximation.Analysis.CollapseUnitaryLift
import GroupApproximation.Analysis.CollapseJoinNonvanishing
import GroupApproximation.Analysis.CollapseDisplacementIdeal
import GroupApproximation.Analysis.CollapseProjectionLift
import GroupApproximation.Analysis.CollapseDiscardCoordinates

/-!
# The printed proof of `thm:projection-collapse`, assembled

Proof-ledger rows `CO.04`, `CO.20`, `CO.21`, `CO.21b`.  Every analytic
ingredient of the printed proof of `thm:projection-collapse` in
`non_mf_groups_exist.tex` is in the corpus; this file walks the printed
argument from its first sentence to the contradiction, in the printed order:

* the symmetric generating set from property (T)
  (`exists_symmetric_generating_pair`);
* the join `q = 1 − ∏_{a∈S}(1 − q_a)` of the displacement supports, nonzero
  because a moved element forces a moved generator
  (`ProjectionOrbitCollapse.exists_mem_conj_ne`,
  `one_sub_listProd_sq_ne_zero`);
* the projection lift `Q_n` of `q` by continuous functional calculus
  (`CollapseProjectionLift.exists_projection_lift`) and the free ultrafilter
  containing the coordinates where it survives — the printed *"discard the
  remaining coordinates"* (`CollapseDiscardCoordinates`);
* the displacements in the ideal `𝓘_q`
  (`CollapseDisplacementIdeal.displacement_mem_rankIdeal`);
* the nonvanishing of `β` from the printed telescoping `∑ e_i = q`
  (`CollapseJoinNonvanishing.exists_lambda_ne_zero_of_join`, with the
  telescoping identity `sum_prefixProd_mul` proved here); and
* the Delorme–Guichardet contradiction
  (`CollapsePrintedContradiction.collapse_contradiction_localized`), whose
  unitary coordinate lifts are `lem:unitarycorona` via
  `CollapseUnitaryLift.coronaAlmostRep`.

The ring-level helpers at the top — the star of a commuting product, the
telescoping sum, idempotence and self-adjointness of a conjugate — are the
pieces of printed arithmetic the corpus stated only in hypothesis position.

`printed_projection_collapse` is the theorem at the subgroup level in `Type 0`;
`Sofic/ProjectionCompressionCollapse.corona_projection_collapse` reaches it
from the manuscript statement by the same universe descent it already used for
the finite-stage route.
-/

namespace GroupApproximation
namespace CollapsePrintedProjectionCollapse

open Filter Matrix Topology
open UltraproductModelConstruction
open ProjectionOrbitCollapse RankNormalizedLambda RankNormalizedHilbertization
open CollapseUnitaryLift
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Ring-level helpers -/

section Ring

variable {A : Type*} [Ring A] [StarRing A]

/-- The star of a product of pairwise commuting self-adjoint elements. -/
theorem star_listProd {l : List A} (hsa : ∀ x ∈ l, star x = x)
    (hc : l.Pairwise Commute) : star l.prod = l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hcomm : Commute a t.prod :=
      Commute.list_prod_right t a (List.pairwise_cons.mp hc).1
    rw [List.prod_cons, star_mul,
      ih (fun x hx ↦ hsa x (List.mem_cons_of_mem a hx))
        (List.pairwise_cons.mp hc).2,
      hsa a List.mem_cons_self]
    exact hcomm.eq.symm

omit [StarRing A] in
/-- **The printed telescoping.**  With `r_i = ∏_{j<i}(1 − q_j)` the products
`e_i = r_i q_i` satisfy `∑_{i<m} e_i = 1 − ∏_{j<m}(1 − q_j)`: each summand is
`r_i − r_{i+1}` and the sum collapses.  Pure ring arithmetic — no commutation,
no idempotence. -/
theorem sum_prefixProd_mul (m : ℕ) (qf : ℕ → A) :
    ∑ i ∈ Finset.range m,
      ((List.range i).map fun j ↦ 1 - qf j).prod * qf i
      = 1 - ((List.range m).map fun j ↦ 1 - qf j).prod := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton]
    noncomm_ring

/-- A list mapped through `f` is the range list mapped through `f` after the
default-valued index lookup.  This is the bridge between the list-shaped join
of `ProjectionOrbitCollapse` and the index-shaped telescoping above. -/
theorem map_eq_range_map {α β : Type*} (l : List α) (d : α) (f : α → β) :
    l.map f = (List.range l.length).map fun i ↦ f (l.getD i d) := by
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  have hlen : i < l.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]

variable {G : Type*} [Group G]

/-- A conjugate of an idempotent is an idempotent. -/
theorem isIdempotentElem_conj (ρ : G →* unitary A) {p : A}
    (hp : IsIdempotentElem p) (g : G) :
    IsIdempotentElem (conj ρ p g) := by
  have hu : star ((ρ g : unitary A) : A) * ((ρ g : unitary A) : A) = 1 :=
    Unitary.star_mul_self_of_mem (ρ g).prop
  have hpp : p * p = p := hp
  show (ρ g : A) * p * star (ρ g : A) * ((ρ g : A) * p * star (ρ g : A))
    = (ρ g : A) * p * star (ρ g : A)
  calc (ρ g : A) * p * star (ρ g : A) * ((ρ g : A) * p * star (ρ g : A))
      = (ρ g : A) * p * (star (ρ g : A) * (ρ g : A)) * p * star (ρ g : A) := by
        noncomm_ring
    _ = (ρ g : A) * (p * p) * star (ρ g : A) := by
        rw [hu]
        noncomm_ring
    _ = (ρ g : A) * p * star (ρ g : A) := by rw [hpp]

/-- A conjugate of a self-adjoint element is self-adjoint. -/
theorem star_conj (ρ : G →* unitary A) {p : A} (hsa : star p = p) (g : G) :
    star (conj ρ p g) = conj ρ p g := by
  show star ((ρ g : A) * p * star (ρ g : A)) = (ρ g : A) * p * star (ρ g : A)
  simp only [star_mul, star_star, hsa, mul_assoc]

/-- Commutation with a unitary makes the conjugate fixed. -/
theorem conj_eq_of_commute (ρ : G →* unitary A) {p : A} {g : G}
    (h : ((ρ g : unitary A) : A) * p = p * ((ρ g : unitary A) : A)) :
    conj ρ p g = p := by
  have hu : ((ρ g : unitary A) : A) * star ((ρ g : unitary A) : A) = 1 :=
    Unitary.mul_star_self_of_mem (ρ g).prop
  show (ρ g : A) * p * star (ρ g : A) = p
  rw [h, mul_assoc, hu, mul_one]

/-- A fixed conjugate makes the unitary commute. -/
theorem commute_of_conj_eq (ρ : G →* unitary A) {p : A} {g : G}
    (h : conj ρ p g = p) :
    ((ρ g : unitary A) : A) * p = p * ((ρ g : unitary A) : A) := by
  have hu : star ((ρ g : unitary A) : A) * ((ρ g : unitary A) : A) = 1 :=
    Unitary.star_mul_self_of_mem (ρ g).prop
  have h' : (ρ g : A) * p * star (ρ g : A) = p := h
  calc (ρ g : A) * p
      = (ρ g : A) * p * (star (ρ g : A) * (ρ g : A)) := by rw [hu, mul_one]
    _ = ((ρ g : A) * p * star (ρ g : A)) * (ρ g : A) := by noncomm_ring
    _ = p * (ρ g : A) := by rw [h']

end Ring

/-! ## The printed theorem, at the subgroup level -/

section Assembly

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-- **`thm:projection-collapse`, by the printed proof.**  `L ≤ H` has property
(T), `s` compresses `L`, `Θ` is a corona representation of `H`, and `p` is a
projection commuting with the compressed image whose `L`-conjugation orbit
commutes pairwise; then `p` commutes with `Θ(L)`.

The proof is the printed one: the displacement supports join to a nonzero
projection `q`, the rank-normalized `Λ` is built on the ideal `𝓘_q`, the
displacements give a nonzero `1`-cocycle for the conjugation representation on
`K_ω`, and Delorme–Guichardet together with the weighted transport chain kills
it.  No finite-stage microstates and no involutive witness appear. -/
theorem printed_projection_collapse {H : Type} [Group H]
    (L : Subgroup H) (hT : HasKazhdanPropertyT.{0, 0} ↥L) {s : H}
    (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (Θ : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (p : NormMatrixCStarCorona (fun n ↦ X n))
    (hsa : star p = p) (hproj : p * p = p)
    (hpcomm : ∀ γ ∈ L,
      ((Θ (s * γ * s⁻¹) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * p
        = p * ((Θ (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)))
    (horb : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute (conj Θ p γ₁) (conj Θ p γ₂)) :
    ∀ γ ∈ L,
      ((Θ γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * p
        = p * ((Θ γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) := by
  classical
  intro γ₀ hγ₀
  by_contra hne0
  set ρ : ↥L →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    Θ.comp L.subtype with hρ_def
  have hpidem : IsIdempotentElem p := hproj
  -- `p` is the orbit projection at `1 ∈ L`, so it commutes with the orbit.
  have hcommP : ∀ b : ↥L, Commute p (conj ρ p b) := by
    intro b
    have h := horb 1 L.one_mem ↑b b.2
    rw [conj_one] at h
    exact h
  have hPidem : ∀ b : ↥L, IsIdempotentElem (conj ρ p b) := fun b ↦
    isIdempotentElem_conj ρ hpidem b
  have horb' : ∀ b₁ b₂ : ↥L, Commute (conj ρ p b₁) (conj ρ p b₂) := fun b₁ b₂ ↦
    horb ↑b₁ b₁.2 ↑b₂ b₂.2
  -- a moved element of `L`
  have hconj0 : conj ρ p ⟨γ₀, hγ₀⟩ ≠ p := by
    intro h
    exact hne0 (commute_of_conj_eq ρ h)
  -- the printed symmetric generating set
  obtain ⟨S, kappa, hone, hsymm, hgen, _hkpos, _hkone, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  obtain ⟨a₀, ha₀S, ha₀ne⟩ := exists_mem_conj_ne ρ p hgen hconj0
  set l : List ↥L := S.toList with hl_def
  have ha₀l : a₀ ∈ l := Finset.mem_toList.2 ha₀S
  have hpairsq : (l.map fun b ↦ (conj ρ p b - p) ^ 2).Pairwise Commute := by
    refine List.pairwise_of_forall_mem_list ?_
    intro x hx y hy
    obtain ⟨b₁, _, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b₂, _, rfl⟩ := List.mem_map.1 hy
    exact commute_sq_sub (hcommP b₁) (hcommP b₂) (horb' b₁ b₂)
  -- the join of the displacement supports
  set qq : NormMatrixCStarCorona (fun n ↦ X n) :=
    1 - ((l.map fun b ↦ (conj ρ p b - p) ^ 2).map fun y ↦ 1 - y).prod
    with hqq_def
  have hqne : qq ≠ 0 := by
    rw [hqq_def]
    exact one_sub_listProd_sq_ne_zero (P := fun b ↦ conj ρ p b) hpidem
      (fun b _ ↦ hPidem b) (fun b _ ↦ hcommP b) hpairsq ha₀l ha₀ne
  -- the join is a self-adjoint idempotent
  have hfactor_idem : ∀ y ∈ (l.map fun b ↦ (conj ρ p b - p) ^ 2),
      IsIdempotentElem y := by
    intro y hy
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hy
    exact isIdempotentElem_sq_sub hpidem (hPidem b) (hcommP b)
  have hfactor_sa : ∀ y ∈ (l.map fun b ↦ (conj ρ p b - p) ^ 2),
      star y = y := by
    intro y hy
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hy
    have hd : star (conj ρ p b - p) = conj ρ p b - p := by
      rw [star_sub, star_conj ρ hsa b, hsa]
    rw [sq, star_mul, hd]
  have hone_sub_idem : ∀ y ∈ ((l.map fun b ↦ (conj ρ p b - p) ^ 2).map
      fun y ↦ 1 - y), IsIdempotentElem y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact (hfactor_idem z hz).one_sub
  have hone_sub_sa : ∀ y ∈ ((l.map fun b ↦ (conj ρ p b - p) ^ 2).map
      fun y ↦ 1 - y), star y = y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    rw [star_sub, star_one, hfactor_sa z hz]
  have hone_sub_pair : ((l.map fun b ↦ (conj ρ p b - p) ^ 2).map
      fun y ↦ 1 - y).Pairwise Commute := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ hpairsq
    intro x y hxy
    exact (Commute.one_left (1 - y)).sub_left
      ((Commute.one_right x).sub_right hxy)
  have hqq_idem : qq * qq = qq := by
    rw [hqq_def]
    exact (isIdempotentElem_listProd hone_sub_idem hone_sub_pair).one_sub
  have hqq_sa : star qq = qq := by
    rw [hqq_def, star_sub, star_one,
      star_listProd hone_sub_sa hone_sub_pair]
  -- the printed projection lift and the printed choice of ultrafilter
  obtain ⟨Q, hQproj, hQmk⟩ :=
    CollapseProjectionLift.exists_projection_lift X qq hqq_sa hqq_idem
  obtain ⟨ω, hω, hrk⟩ :=
    CollapseDiscardCoordinates.exists_free_ultrafilter_rank_pos X Q hQproj
      (by rw [hQmk]; exact hqne)
  have hQrc : Q ∈ rankControlled X (coord X Q) := by
    refine ⟨1, fun n ↦ ?_⟩
    show (Q n).rank ≤ 1 * (Q n).rank
    rw [one_mul]
  have hqmem : qq ∈ rankIdeal X (coord X Q) := by
    rw [← hQmk]
    exact (mem_rankIdeal_iff X (coord X Q) _).2 ⟨⟨Q, hQrc⟩, rfl⟩
  -- the displacements lie in the ideal
  have hSjoin : ∀ a ∈ (↑S : Set ↥L),
      (conj ρ p a - p) * qq = conj ρ p a - p := by
    intro a haS
    rw [hqq_def]
    exact CollapseDisplacementIdeal.displacement_mul_join ρ p hpidem l
      (fun b _ ↦ hPidem b) (fun b _ ↦ hcommP b) hpairsq
      (Finset.mem_toList.2 (Finset.mem_coe.1 haS))
  have hmem : ∀ γ : ↥L, conj ρ p γ - p ∈ rankIdeal X (coord X Q) := by
    intro γ
    have hγtop : γ ∈ Subgroup.closure (↑S : Set ↥L) := by
      rw [hgen]
      exact Subgroup.mem_top γ
    exact CollapseDisplacementIdeal.displacement_mem_rankIdeal X (coord X Q) ρ
      p qq hqmem ↑S hSjoin hγtop
  -- the almost representation of the printed unitary lifts
  haveI : ∀ n, Nonempty ((coronaAlmostRep X Θ).model n) := fun n ↦
    Fintype.card_pos_iff.mp ((coronaAlmostRep X Θ).modelNonempty n)
  have hlift : ∀ g : H,
      coronaLinear X (unitarySequenceBounded X
          (fun n ↦ (coronaAlmostRep X Θ).map n g))
        = ((Θ g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) :=
    fun g ↦ congrArg
      (fun t : unitary (NormMatrixCStarCorona (fun n ↦ X n)) ↦
        (t : NormMatrixCStarCorona (fun n ↦ X n)))
      (unitarySequenceToCorona_liftFam X Θ g)
  have hd : ∀ g h : H,
      (conj Θ p (g * h) - p)
        = (conj Θ p g - p)
          + coronaLinear X (unitarySequenceBounded X
              (fun n ↦ (coronaAlmostRep X Θ).map n g)) *
            (conj Θ p h - p) *
            star (coronaLinear X (unitarySequenceBounded X
              (fun n ↦ (coronaAlmostRep X Θ).map n g))) := by
    intro g h
    rw [hlift g]
    exact sub_conj_mul Θ p g h
  have hcompressed : ∀ γ : ↥L,
      conj Θ p (s * L.subtype γ * s⁻¹) - p = 0 := by
    intro γ
    rw [sub_eq_zero]
    exact conj_eq_of_commute Θ (hpcomm ↑γ γ.2)
  -- the nonvanishing of the cocycle, from the printed join
  have hcommR : ∀ i : ℕ, Commute (conj ρ p (l.getD i 1) - p)
      (((List.range i).map
        fun j ↦ 1 - (conj ρ p (l.getD j 1) - p) ^ 2).prod) := by
    intro i
    refine Commute.list_prod_right _ _ ?_
    intro y hy
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hy
    exact (Commute.one_right _).sub_right
      ((commute_sub (hcommP (l.getD i 1)) (hcommP (l.getD j 1))
        (horb' (l.getD i 1) (l.getD j 1))).pow_right 2)
  have htele := sum_prefixProd_mul l.length
    (fun j ↦ (conj ρ p (l.getD j 1) - p) ^ 2)
  have hlists : ((List.range l.length).map
        fun j ↦ 1 - (conj ρ p (l.getD j 1) - p) ^ 2).prod
      = ((l.map fun b ↦ (conj ρ p b - p) ^ 2).map fun y ↦ 1 - y).prod := by
    congr 1
    rw [List.map_map]
    exact (map_eq_range_map l 1 fun b ↦ 1 - (conj ρ p b - p) ^ 2).symm
  have hqsum : qq = ∑ i ∈ Finset.range l.length,
      ((conj ρ p (l.getD i 1) - p) *
          ((List.range i).map
            fun j ↦ 1 - (conj ρ p (l.getD j 1) - p) ^ 2).prod)
        * (conj ρ p (l.getD i 1) - p) * 1 := by
    rw [hqq_def, ← hlists, ← htele]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [mul_one, (hcommR i).eq, mul_assoc, ← sq]
  obtain ⟨i0, hi0⟩ := CollapseJoinNonvanishing.exists_lambda_ne_zero_of_join X
    Q ω hω hQproj hrk l.length
    (fun i ↦ ⟨((conj ρ p (l.getD i 1) - p) *
        ((List.range i).map
          fun j ↦ 1 - (conj ρ p (l.getD j 1) - p) ^ 2).prod)
      * (conj ρ p (l.getD i 1) - p) * 1,
      mul_mem_rankIdeal X (coord X Q) _ _ (hmem (l.getD i 1))⟩)
    (fun i ↦ ⟨conj ρ p (l.getD i 1) - p, hmem (l.getD i 1)⟩)
    (fun i ↦ (conj ρ p (l.getD i 1) - p) *
        ((List.range i).map
          fun j ↦ 1 - (conj ρ p (l.getD j 1) - p) ^ 2).prod)
    (fun i ↦ rfl)
    ⟨qq, hqmem⟩ hQmk.symm hqsum
  -- the printed contradiction
  exact CollapsePrintedContradiction.collapse_contradiction_localized
    (coronaAlmostRep X Θ) ω hω hT L.subtype s
    (fun γ ↦ ⟨⟨s * ↑γ * s⁻¹, hcomp ↑γ γ.2⟩, rfl⟩)
    (coord X Q) (fun g ↦ conj Θ p g - p) hd hmem hcompressed
    ⟨l.getD i0 1, hi0⟩

end Assembly

end

end CollapsePrintedProjectionCollapse
end GroupApproximation
