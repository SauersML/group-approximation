import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFConverse
import GroupApproximation.Meta.AxiomGuard

/-!
# A double-coset normal form for the Schreier gap (lane bh-met-77n)

Notation: `Q = higmanVCCommon_Q d`, `E = higmanVCTreeNF_E d : Q →* V_d`, `U = higmanVCTreeNF_U d`
(the faithful balanced subgroup), `K = normalClosure (higmanVC_rels d fun _ => True)`, and
`t = mk (of (a, b))` for the pivot.

**Why a double-coset normal form.**  Take `X = V_d` acting on the right through `E`, with an
exact section `c`.  Then the Schreier condition forces `c (x * E g) = c x * g`, which is just the
level statement again.  So `X` must be at least as coarse as the cosets `E(U) \ V_d`.  Here we go
one step further, to the double cosets `E(U) \ V_d / E(U)`, which are the defect distributions.
Only the pivot can move between them.

**Gap: `HigmanVCTreeNFWitStatement`.**  For every `d > 1` and arbitrarily large `n` we need a
pivot `(a, b)` of lengths `(n, n + 1)` and a map `τ : Q → Q` satisfying two conditions.
* `higmanVCTreeNFWit_IsNF d τ` holds:
  * (0) `τ` is constant on `E`-double cosets;
  * (i) `E (τ q) ∈ E(U) E(q) E(U)`;
  * (ii) `E q ∈ E(U) → τ q ∈ U`.
* `higmanVCTreeNFWit_PivotClosed d τ t` holds: (iii) `τ q * u * t ∈ U τ(q') U` for some `q'`,
  for every `q` and every `u ∈ U`.

Conditions (0) to (ii) are **constructible with no hypotheses**.  Take `higmanVCTreeNFWit_tau`,
a quotient representative that is `1` on the trivial class (`EnvelopeHigmanVCTreeNFWitConverse`).
So the only real content is (iii).  There is one pivot condition per double coset, with no
`Q`-set, no action and no balanced-letter checks.

**Proved here.**
* `higmanVCTreeNFWit_level_of_dc : HigmanVCTreeNFWitStatement → HigmanVCTreeLevelStatement`.
  This proof is **direct**.  Let `S = ⋃ U τ(q) U`.  Then `1 ∈ S` by (ii), and `S` is closed
  under `· * U` and, by (iii), under `· * t`.  Every generator of `G_n` is an involution
  (`higmanVCCommon_mk_sq`), so `G_n` lies in the stabiliser of `S`.  Hence `mk r ∈ S` for
  `r ∈ ker` with `mk r ∈ G_n`.  Write `mk r = u₁ τ(q) u₂`.  Then `E (mk r) = 1`, so (i) gives
  `E q ∈ E(U)`, and (ii) gives `τ q ∈ U`, so `mk r ∈ U`.  Faithfulness of `U` gives `r ∈ K`.
  No local conjugation property is needed.
* The defect / balanced / (1) endpoints follow from the corpus wires.
* `higmanVCTreeNFWit_schreier_of_dc` gives `HigmanVCTreeNFSchreierStatement`.  **LOUD: this goes
  through (1) and the converse `higmanVCTreeNF_schreier_of_ker_le`.**  A direct coset witness
  (`X = E(U) \ V_d`) would also need the local conjugation property, which is not supplied.

**LOUD truth status.**  The Statement is **equivalent to (1) as a Prop**
(`higmanVCTreeNFWit_iff_ker_le` in `EnvelopeHigmanVCTreeNFWitConverse`).  It is NOT strictly
weaker as a Prop; under (1) the canonical `τ` works.  It is strictly smaller in *proof content*
than `HigmanVCTreeNFSchreierStatement`.  `scratchpad/bh-met-77n/check.py` tests the wire on
finite central-extension models (D8, D12, D16, S3×Z2, D8×Z2, S4, Q8; 1852 configurations); no
counterexample to the wire was found.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `q'` lies in the `E(U)`-double coset of `q`, read in `V_d`. -/
def higmanVCTreeNFWit_dc (d : ℕ) (q q' : higmanVCCommon_Q d) : Prop :=
  ∃ β ∈ higmanVCTreeNF_U d, ∃ β' ∈ higmanVCTreeNF_U d,
    higmanVCTreeNF_E d q' = higmanVCTreeNF_E d β * higmanVCTreeNF_E d q * higmanVCTreeNF_E d β'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_dc

theorem higmanVCTreeNFWit_dc_iff {d : ℕ} {q q' : higmanVCCommon_Q d} :
    higmanVCTreeNFWit_dc d q q' ↔ ∃ β ∈ higmanVCTreeNF_U d, ∃ β' ∈ higmanVCTreeNF_U d,
      higmanVCTreeNF_E d q' =
        higmanVCTreeNF_E d β * higmanVCTreeNF_E d q * higmanVCTreeNF_E d β' :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_dc_iff

/-- A **double-coset normal form**: conditions (0), (i) and (ii). -/
def higmanVCTreeNFWit_IsNF (d : ℕ) (τ : higmanVCCommon_Q d → higmanVCCommon_Q d) : Prop :=
  (∀ q q', higmanVCTreeNFWit_dc d q q' → τ q' = τ q) ∧
  (∀ q, higmanVCTreeNFWit_dc d q (τ q)) ∧
  (∀ q, ∀ β ∈ higmanVCTreeNF_U d, higmanVCTreeNF_E d q = higmanVCTreeNF_E d β →
    τ q ∈ higmanVCTreeNF_U d)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_IsNF

/-- Condition (iii): right multiplication by the pivot `t` preserves `⋃ U τ(q) U`. -/
def higmanVCTreeNFWit_PivotClosed (d : ℕ) (τ : higmanVCCommon_Q d → higmanVCCommon_Q d)
    (t : higmanVCCommon_Q d) : Prop :=
  ∀ q, ∀ u ∈ higmanVCTreeNF_U d, ∃ u₁ ∈ higmanVCTreeNF_U d, ∃ q', ∃ u₂ ∈ higmanVCTreeNF_U d,
    τ q * u * t = u₁ * τ q' * u₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_PivotClosed

/-- **The remaining gap (lane bh-met-77n): a pivot-closed double-coset normal form.**
LOUD: equivalent to (1) as a Prop; smaller in proof content (only (iii) is non-constructive). -/
def HigmanVCTreeNFWitStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d),
    a.length = n ∧ b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧
    ∃ τ : higmanVCCommon_Q d → higmanVCCommon_Q d, higmanVCTreeNFWit_IsNF d τ ∧
      higmanVCTreeNFWit_PivotClosed d τ (higmanVCCommon_mk d (FreeGroup.of (a, b)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTreeNFWitStatement

/-- The union `⋃_q U τ(q) U`. -/
def higmanVCTreeNFWit_S (d : ℕ) (τ : higmanVCCommon_Q d → higmanVCCommon_Q d) :
    Set (higmanVCCommon_Q d) :=
  {s | ∃ u₁ ∈ higmanVCTreeNF_U d, ∃ q, ∃ u₂ ∈ higmanVCTreeNF_U d, s = u₁ * τ q * u₂}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_S

theorem higmanVCTreeNFWit_mem_S {d : ℕ} {τ : higmanVCCommon_Q d → higmanVCCommon_Q d}
    {s : higmanVCCommon_Q d} : s ∈ higmanVCTreeNFWit_S d τ ↔
      ∃ u₁ ∈ higmanVCTreeNF_U d, ∃ q, ∃ u₂ ∈ higmanVCTreeNF_U d, s = u₁ * τ q * u₂ :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_mem_S

/-- The right stabiliser `{g | ∀ s, s ∈ S ↔ s * g ∈ S}` of a set, as a subgroup. -/
def higmanVCTreeNFWit_stab {G : Type*} [Group G] (S : Set G) : Subgroup G where
  carrier := {g | ∀ s, s ∈ S ↔ s * g ∈ S}
  mul_mem' := fun {a b} ha hb s => by
    rw [← mul_assoc]
    exact (ha s).trans (hb (s * a))
  one_mem' := fun s => by
    rw [mul_one]
  inv_mem' := fun {a} ha s => by
    have h := ha (s * a⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_stab

theorem higmanVCTreeNFWit_mem_stab {G : Type*} [Group G] {S : Set G} {g : G} :
    g ∈ higmanVCTreeNFWit_stab S ↔ ∀ s, s ∈ S ↔ s * g ∈ S :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_mem_stab

/-- An involution that maps `S` into itself stabilises `S`. -/
theorem higmanVCTreeNFWit_mem_stab_of_sq {G : Type*} [Group G] {S : Set G} {g : G}
    (hg : g * g = 1) (hS : ∀ s ∈ S, s * g ∈ S) : g ∈ higmanVCTreeNFWit_stab S := by
  refine higmanVCTreeNFWit_mem_stab.mpr fun s => ⟨hS s, fun h => ?_⟩
  have h' := hS _ h
  rwa [mul_assoc, hg, mul_one] at h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_mem_stab_of_sq

theorem higmanVCTreeNFWit_one_mem_S {d : ℕ} {τ : higmanVCCommon_Q d → higmanVCCommon_Q d}
    (hτ : higmanVCTreeNFWit_IsNF d τ) : (1 : higmanVCCommon_Q d) ∈ higmanVCTreeNFWit_S d τ := by
  have h1 : τ 1 ∈ higmanVCTreeNF_U d := hτ.2.2 1 1 (higmanVCTreeNF_U d).one_mem rfl
  refine higmanVCTreeNFWit_mem_S.mpr
    ⟨(τ 1)⁻¹, (higmanVCTreeNF_U d).inv_mem h1, 1, 1, (higmanVCTreeNF_U d).one_mem, ?_⟩
  rw [inv_mul_cancel, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_one_mem_S

theorem higmanVCTreeNFWit_S_mul_U {d : ℕ} {τ : higmanVCCommon_Q d → higmanVCCommon_Q d}
    {s u : higmanVCCommon_Q d} (hs : s ∈ higmanVCTreeNFWit_S d τ) (hu : u ∈ higmanVCTreeNF_U d) :
    s * u ∈ higmanVCTreeNFWit_S d τ := by
  obtain ⟨u₁, hu₁, q, u₂, hu₂, rfl⟩ := higmanVCTreeNFWit_mem_S.mp hs
  exact higmanVCTreeNFWit_mem_S.mpr
    ⟨u₁, hu₁, q, u₂ * u, (higmanVCTreeNF_U d).mul_mem hu₂ hu, mul_assoc (u₁ * τ q) u₂ u⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_S_mul_U

theorem higmanVCTreeNFWit_S_mul_t {d : ℕ} {τ : higmanVCCommon_Q d → higmanVCCommon_Q d}
    {t : higmanVCCommon_Q d} (ht : higmanVCTreeNFWit_PivotClosed d τ t) {s : higmanVCCommon_Q d}
    (hs : s ∈ higmanVCTreeNFWit_S d τ) : s * t ∈ higmanVCTreeNFWit_S d τ := by
  obtain ⟨u₁, hu₁, q, u₂, hu₂, rfl⟩ := higmanVCTreeNFWit_mem_S.mp hs
  obtain ⟨v₁, hv₁, q', v₂, hv₂, e⟩ := ht q u₂ hu₂
  refine higmanVCTreeNFWit_mem_S.mpr
    ⟨u₁ * v₁, (higmanVCTreeNF_U d).mul_mem hu₁ hv₁, q', v₂, hv₂, ?_⟩
  rw [mul_assoc u₁ (τ q) u₂, mul_assoc u₁ (τ q * u₂) t, e]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_S_mul_t

/-- Every element of `G_n` stabilises `S`, and in particular lies in `S`. -/
theorem higmanVCTreeNFWit_mem_S_of_G {d n : ℕ} {a b : List (Fin d)}
    {τ : higmanVCCommon_Q d → higmanVCCommon_Q d} (hτ : higmanVCTreeNFWit_IsNF d τ)
    (ht : higmanVCTreeNFWit_PivotClosed d τ (higmanVCCommon_mk d (FreeGroup.of (a, b))))
    {q : higmanVCCommon_Q d} (hq : q ∈ higmanVCTreeLevel_G d n a b) :
    q ∈ higmanVCTreeNFWit_S d τ := by
  rw [higmanVCTreeLevel_G] at hq
  have hT : Subgroup.closure (higmanVCTreeLevel_gens d n a b) ≤
      higmanVCTreeNFWit_stab (higmanVCTreeNFWit_S d τ) := by
    refine (Subgroup.closure_le _).mpr fun g hg => ?_
    rw [higmanVCTreeLevel_gens, Set.mem_setOf_eq] at hg
    rcases hg with ⟨x, y, hx, hy, rfl⟩ | rfl
    · exact higmanVCTreeNFWit_mem_stab_of_sq (higmanVCCommon_mk_sq x y) fun _ hs =>
        higmanVCTreeNFWit_S_mul_U hs (higmanVCTreeNF_letter_mem (hx.trans hy.symm))
    · exact higmanVCTreeNFWit_mem_stab_of_sq (higmanVCCommon_mk_sq a b) fun _ hs =>
        higmanVCTreeNFWit_S_mul_t ht hs
  have h1 := (higmanVCTreeNFWit_mem_stab.mp (hT hq) 1).mp (higmanVCTreeNFWit_one_mem_S hτ)
  rwa [one_mul] at h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_mem_S_of_G

/-- Solving `x * (b * y * b') * z = 1` for `y`. -/
theorem higmanVCTreeNFWit_solve {G : Type*} [Group G] {x y z b b' : G}
    (h : x * (b * y * b') * z = 1) : y = b⁻¹ * x⁻¹ * z⁻¹ * b'⁻¹ := by
  have h1 : x * (b * y * b') = z⁻¹ := mul_eq_one_iff_eq_inv.mp h
  have h2 : b * y * b' = x⁻¹ * z⁻¹ := eq_inv_mul_of_mul_eq h1
  have h3 : b * y = x⁻¹ * z⁻¹ * b'⁻¹ := eq_mul_inv_of_mul_eq h2
  have h4 : y = b⁻¹ * (x⁻¹ * z⁻¹ * b'⁻¹) := eq_inv_mul_of_mul_eq h3
  rw [h4]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_solve

/-- **Reduction (proved, direct):** a pivot-closed double-coset normal form gives the level
gap. -/
theorem higmanVCTreeNFWit_level_of_dc (h : HigmanVCTreeNFWitStatement) :
    HigmanVCTreeLevelStatement := by
  intro d hd N
  obtain ⟨n, hN, a, b, ha, hb, hab, hba, τ, hτ, ht⟩ := h d hd N
  refine ⟨n, hN, a, b, ha, hb, hab, hba, fun r hr hG => ?_⟩
  obtain ⟨u₁, hu₁, q, u₂, hu₂, e⟩ :=
    higmanVCTreeNFWit_mem_S.mp (higmanVCTreeNFWit_mem_S_of_G hτ ht hG)
  obtain ⟨β, hβ, β', hβ', hq⟩ := higmanVCTreeNFWit_dc_iff.mp (hτ.2.1 q)
  have hE : higmanVCTreeNF_E d (higmanVCCommon_mk d r) = 1 := by
    rw [higmanVCTreeNF_E_mk]
    exact MonoidHom.mem_ker.mp hr
  rw [e, map_mul, map_mul, hq] at hE
  have hτq : τ q ∈ higmanVCTreeNF_U d := by
    refine hτ.2.2 q (β⁻¹ * u₁⁻¹ * u₂⁻¹ * β'⁻¹) ?_ ?_
    · exact (higmanVCTreeNF_U d).mul_mem ((higmanVCTreeNF_U d).mul_mem
        ((higmanVCTreeNF_U d).mul_mem ((higmanVCTreeNF_U d).inv_mem hβ)
          ((higmanVCTreeNF_U d).inv_mem hu₁)) ((higmanVCTreeNF_U d).inv_mem hu₂))
        ((higmanVCTreeNF_U d).inv_mem hβ')
    · simp only [map_mul, map_inv]
      exact higmanVCTreeNFWit_solve hE
  refine higmanVCTreeNF_U_faithful (by omega) hr ?_
  rw [e]
  exact (higmanVCTreeNF_U d).mul_mem ((higmanVCTreeNF_U d).mul_mem hu₁ hτq) hu₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_level_of_dc

/-- **Wire to the defect gap** of lane bh-met-77i. -/
theorem higmanVCTreeNFWit_defect_of_dc (h : HigmanVCTreeNFWitStatement) :
    HigmanVCTreeDefectStatement :=
  higmanVCTreeLevel_defect_of_level (higmanVCTreeNFWit_level_of_dc h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_defect_of_dc

/-- **Endpoint:** the double-coset normal form gives (1). -/
theorem higmanVCTreeNFWit_ker_le_of_dc (h : HigmanVCTreeNFWitStatement) (d : ℕ) (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  higmanVCTreeLevel_ker_le_of_level (higmanVCTreeNFWit_level_of_dc h) d hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_ker_le_of_dc

/-- **The Schreier gap from the double-coset normal form.**  LOUD: routed through (1) and the
converse `higmanVCTreeNF_schreier_of_ker_le` (trivial witness `X = Q`), not a direct coset
witness. -/
theorem higmanVCTreeNFWit_schreier_of_dc (h : HigmanVCTreeNFWitStatement) :
    HigmanVCTreeNFSchreierStatement :=
  higmanVCTreeNF_schreier_of_ker_le (higmanVCTreeNFWit_ker_le_of_dc h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_schreier_of_dc

end GroupApproximation.BooneHigman.Metabelian.Envelope
