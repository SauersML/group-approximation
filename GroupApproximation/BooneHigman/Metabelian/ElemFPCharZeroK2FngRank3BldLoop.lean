import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngRank3BldWord
import GroupApproximation.Meta.AxiomGuard

/-!
# The Schreier-loop residual for `czK2FngRank3Sec_ResidualStatement` (lane `bh-met-93y`)

Put `S = ℤ[1/(mp)]`, `φ : ℤ[1/m] → S`, `Γ = φ(E_3(ℤ[1/m]))` and `X = E_3(S)/Γ`, with standard
vertex `y₀ = Γ`.  `F` is the free group on the four letters `a₀₁, a₁₂, a₂₀, u₀₁`
(`czK2FngRank3Bld_Word`).  It acts on `X` through `evE : F → E_3(S)`.

**The new residual `czK2FngRank3Bld_LoopStatement`.**  It is purely about matrices: no
Steinberg group and no `K₂`.  There is a finite set `L` of relator words (`evE ℓ = 1`) such
that every word fixing `y₀` (a closed edge-path at `y₀` in the Schreier graph of `X`) lies in
`⟪L⟫ · ⟨a₀₁, a₁₂, a₂₀, u₀₁ ^ p⟩`.  That is, the closed paths are products of lassos of
finitely many short loops, together with the four base loops, which fix `y₀`.

**Proved outright.**
* `czK2FngRank3Bld_residual_of_loop`: the loop statement gives
  `czK2FngRank3Sec_ResidualStatement`, with `s = evSt '' L`.  Every `g` with `projection g ∈ Γ`
  lies in `Q` (`czK2FngRank3Bld_mem_Q_of_stab`), so `K₂ ≤ Q`, hence `K₂ ≤ N`
  (`czK2FngGtOneRank3_mem_N_of_mem_Q`), and the section exists
  (`czK2FngGtOneRank3_exists_section`).
* `czK2FngRank3Bld_rankThree_of_loop`: the loop statement gives
  `czK2FngGtOne_RankThreeStatement`.
* `czK2FngRank3Bld_fix_of_mem`: the converse inclusion.  Every word of
  `⟪L⟫ ⊔ ⟨base loops⟩` fixes `y₀`.  So the statement says `Stab_F(y₀) = ⟪L⟫ ⊔ ⟨base loops⟩`,
  which is the Schreier reading of `π₁`.

**Strength (LOUD).**
* It is **not** proved equivalent to the old residual.  Only `Loop → Residual` is proved.  The
  converse would need finite presentation of `St_3(S)` relative to `St_3(ℤ[1/m])`.
* It does not mention `K₂`, Steinberg groups, sections or `Q`.  It is a relative finite
  presentation of `E_3(S)` over the base loops, i.e. simple connectivity of the Schreier
  graph modulo finitely many 2-cells.  It is **not** "`E_3(S)` is finitely presented": the base
  loop subgroup is free to use, and it is never required to be finitely presented.
* WARNING: it is close in spirit to a presentation statement.  It is a *relative* one, and no
  finite presentation is assumed anywhere.

**Truth.**  It is true since `E_3(ℤ[1/(mp)]) = SL_3(ℤ[1/(mp)])` is finitely presented (Behr),
as a truth argument only.  With a finite presentation, `Stab_F(y₀)` is the preimage of `Γ`,
and `Γ` is finitely generated (by the images of the base loops), so the stabiliser is
`⟪relators⟫ ⊔ ⟨finitely many lifts⟩`.  The script `$SP/bh-met-93y/truth_check.py` checks, on
the `p`-local lattice model for `p = 2, 3` and small `m`: `a₀₁, a₁₂, a₂₀` fix `y₀`; `u₀₁ ^ k`
fixes `y₀` iff `p ∣ k`; `u₀₁ ^ p = e₀₁(1/m)`; the ball sizes; that the cycle rank is positive
(so `L` must be nonempty); that the images generate `SL_3(𝔽_q)` for `q = 5, 7`; and the
relator `[a₀₁, u₀₁]`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- The vertex set `X = E_3(ℤ[1/(mp)])/φ(E_3(ℤ[1/m]))`. -/
abbrev czK2FngRank3Bld_X (m p : ℕ) : Type :=
  elementaryGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) ⧸
    (elementaryGroupMap (ι := Fin 3) (czK2FngGtOneRank3_locMap m p)).range

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_X

/-- **The Schreier-loop residual (lane `bh-met-93y`).**  Finitely many relator words `L`,
together with the four base loops, normally generate every closed path at `y₀`. -/
def czK2FngRank3Bld_LoopStatement : Prop :=
  ∀ m p : ℕ, 0 < m → p.Prime → ¬ p ∣ m →
    ∃ L : Set (FreeGroup czK2FngRank3Bld_Letter), L.Finite ∧
      (∀ ℓ ∈ L, czK2FngRank3Bld_evE m p ℓ = 1) ∧
      ∀ w : FreeGroup czK2FngRank3Bld_Letter,
        czK2FngRank3Bld_evE m p w • (QuotientGroup.mk 1 : czK2FngRank3Bld_X m p) =
          QuotientGroup.mk 1 →
        w ∈ Subgroup.normalClosure L ⊔ Subgroup.closure (czK2FngRank3Bld_baseLoops p)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_LoopStatement

/-- `e` fixes the standard vertex iff `e ∈ Γ`. -/
theorem czK2FngRank3Bld_smul_vertex_iff (m p : ℕ)
    (e : elementaryGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))) :
    e • (QuotientGroup.mk 1 : czK2FngRank3Bld_X m p) = QuotientGroup.mk 1 ↔
      e ∈ (elementaryGroupMap (ι := Fin 3) (czK2FngGtOneRank3_locMap m p)).range := by
  have h : (QuotientGroup.mk (e * 1) : czK2FngRank3Bld_X m p) =
      e • (QuotientGroup.mk 1 : czK2FngRank3Bld_X m p) :=
    rfl
  rw [← h, mul_one]
  refine ⟨fun h' ↦ ?_, fun he ↦ QuotientGroup.eq.mpr (by rw [mul_one]; exact inv_mem he)⟩
  have h'' := QuotientGroup.eq.mp h'
  rwa [mul_one, inv_mem_iff] at h''

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_smul_vertex_iff

/-- The base loops evaluate into `Γ`. -/
theorem czK2FngRank3Bld_evE_baseLoops (m p : ℕ) (b : FreeGroup czK2FngRank3Bld_Letter)
    (hb : b ∈ czK2FngRank3Bld_baseLoops p) :
    czK2FngRank3Bld_evE m p b ∈
      (elementaryGroupMap (ι := Fin 3) (czK2FngGtOneRank3_locMap m p)).range := by
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (czK2FngRank3Bld_evSt_baseLoops m p b hb)
  rw [← czK2FngRank3Bld_projection_evSt, ← hv, projection_ringMap]
  exact MonoidHom.mem_range.mpr ⟨projection v, rfl⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_evE_baseLoops

/-- **Converse inclusion.**  Every word of `⟪L⟫ ⊔ ⟨base loops⟩` fixes the standard vertex,
when every relator word evaluates to `1`. -/
theorem czK2FngRank3Bld_fix_of_mem (m p : ℕ) (L : Set (FreeGroup czK2FngRank3Bld_Letter))
    (hL1 : ∀ ℓ ∈ L, czK2FngRank3Bld_evE m p ℓ = 1) {w : FreeGroup czK2FngRank3Bld_Letter}
    (hw : w ∈ Subgroup.normalClosure L ⊔ Subgroup.closure (czK2FngRank3Bld_baseLoops p)) :
    czK2FngRank3Bld_evE m p w • (QuotientGroup.mk 1 : czK2FngRank3Bld_X m p) =
      QuotientGroup.mk 1 := by
  have hker : Subgroup.normalClosure L ≤ (czK2FngRank3Bld_evE m p).ker :=
    Subgroup.normalClosure_le_normal fun ℓ hℓ ↦ MonoidHom.mem_ker.mpr (hL1 ℓ hℓ)
  have hle : Subgroup.normalClosure L ⊔ Subgroup.closure (czK2FngRank3Bld_baseLoops p) ≤
      (elementaryGroupMap (ι := Fin 3) (czK2FngGtOneRank3_locMap m p)).range.comap
        (czK2FngRank3Bld_evE m p) := by
    refine sup_le (hker.trans fun v hv ↦ ?_) ?_
    · rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hv]
      exact one_mem _
    · rw [Subgroup.closure_le]
      exact fun b hb ↦ Subgroup.mem_comap.mpr (czK2FngRank3Bld_evE_baseLoops m p b hb)
  exact (czK2FngRank3Bld_smul_vertex_iff m p _).mpr (Subgroup.mem_comap.mp (hle hw))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_fix_of_mem

/-- **The key step.**  Under the loop property for `L`, every `g` with `projection g ∈ Γ` lies
in `Q = Φ(St_3(ℤ[1/m])) ⊔ ⟪Φ(K₂(3, ℤ[1/m])) ∪ evSt '' L⟫`. -/
theorem czK2FngRank3Bld_mem_Q_of_stab (m p : ℕ) (L : Set (FreeGroup czK2FngRank3Bld_Letter))
    (hloop : ∀ w : FreeGroup czK2FngRank3Bld_Letter,
      czK2FngRank3Bld_evE m p w • (QuotientGroup.mk 1 : czK2FngRank3Bld_X m p) =
        QuotientGroup.mk 1 →
      w ∈ Subgroup.normalClosure L ⊔ Subgroup.closure (czK2FngRank3Bld_baseLoops p))
    {g : SteinbergGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))}
    (hg : projection g ∈
      (elementaryGroupMap (ι := Fin 3) (czK2FngGtOneRank3_locMap m p)).range) :
    g ∈ czK2FngGtOneRank3_Q (czK2FngGtOneRank3_locMap m p)
      (czK2FngRank3Bld_evSt m p '' L) := by
  obtain ⟨w, rfl⟩ := czK2FngRank3Bld_evSt_surjective m p g
  have hfix : czK2FngRank3Bld_evE m p w • (QuotientGroup.mk 1 : czK2FngRank3Bld_X m p) =
      QuotientGroup.mk 1 := by
    refine (czK2FngRank3Bld_smul_vertex_iff m p _).mpr ?_
    rw [← czK2FngRank3Bld_projection_evSt]
    exact hg
  have hmap : (Subgroup.normalClosure L ⊔
      Subgroup.closure (czK2FngRank3Bld_baseLoops p)).map (czK2FngRank3Bld_evSt m p) ≤
      czK2FngGtOneRank3_Q (czK2FngGtOneRank3_locMap m p) (czK2FngRank3Bld_evSt m p '' L) := by
    unfold czK2FngGtOneRank3_Q czK2FngGtOneRank3_N
    rw [Subgroup.map_sup]
    refine sup_le ((Subgroup.map_normalClosure_le L _).trans ?_) ?_
    · exact le_sup_of_le_right (Subgroup.normalClosure_mono Set.subset_union_right)
    · refine le_sup_of_le_left ?_
      rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      exact fun b hb ↦ Subgroup.mem_comap.mpr (czK2FngRank3Bld_evSt_baseLoops m p b hb)
  exact hmap (Subgroup.mem_map_of_mem _ (hloop w hfix))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_mem_Q_of_stab

/-- **The loop statement gives the residual** `czK2FngRank3Sec_ResidualStatement`. -/
theorem czK2FngRank3Bld_residual_of_loop (h : czK2FngRank3Bld_LoopStatement) :
    czK2FngRank3Sec_ResidualStatement := by
  intro m p hm hp hpm
  obtain ⟨L, hLfin, hL1, hloop⟩ := h m p hm hp hpm
  have hmp : m * p ≠ 0 := Nat.mul_ne_zero hm.ne' hp.ne_zero
  have hsK : czK2FngRank3Bld_evSt m p '' L ⊆
      (K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) :
        Set (SteinbergGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)))) := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    exact (mem_K2_iff _).mpr (by rw [czK2FngRank3Bld_projection_evSt]; exact hL1 ℓ hℓ)
  have hle : K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) ≤
      czK2FngGtOneRank3_N (czK2FngGtOneRank3_locMap m p) (czK2FngRank3Bld_evSt m p '' L) := by
    intro k hk
    have hkQ := czK2FngRank3Bld_mem_Q_of_stab m p L hloop (g := k)
      (by rw [(mem_K2_iff k).mp hk]; exact one_mem _)
    exact czK2FngGtOneRank3_mem_N_of_mem_Q (czK2FngGtOneRank3_locMap m p)
      (czK2FngGtOneRank3_locMap_injective m p hmp) _ hsK hkQ hk
  exact ⟨czK2FngRank3Bld_evSt m p '' L, hLfin.image _, hsK,
    czK2FngRank3Sec_cyclic_of_sectionProp _ _ _
      (czK2FngGtOneRank3_exists_section _ _ hle _)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_residual_of_loop

/-- **The loop statement gives the target** `czK2FngGtOne_RankThreeStatement`. -/
theorem czK2FngRank3Bld_rankThree_of_loop (h : czK2FngRank3Bld_LoopStatement) :
    czK2FngGtOne_RankThreeStatement :=
  czK2FngRank3Sec_rankThree_of_residual (czK2FngRank3Bld_residual_of_loop h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_rankThree_of_loop

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
