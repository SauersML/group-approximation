import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFBal
import GroupApproximation.Meta.AxiomGuard

/-!
# A Schreier-transversal normal form for the level gap (lane bh-met-77l)

Write `K = normalClosure (higmanVC_rels d fun _ => True)`, `Q = higmanVCCommon_Q d`,
`E : Q →* V_d` for the evaluation (`higmanVCTreeNF_E`), and `U ≤ Q` for the faithful balanced
subgroup of `EnvelopeHigmanVCTreeNFBal`.

**Proved here, with no hypotheses.**
* `higmanVCTreeNF_telescope` is the generic Schreier / Reidemeister telescoping lemma.  Take a
  right action `act` of a group `G` on a set `X` and a "transversal" `c : X → G`.  If every
  generator `g ∈ S` has all its Schreier elements `c x * g * c (x • g)⁻¹` in `U`, then so does
  every element of `closure S`.  The word induction (products and inverses) is done once here.
* `higmanVCTreeNF_level_of_schreier : HigmanVCTreeNFSchreierStatement →
  HigmanVCTreeLevelStatement`, and hence (1) (`higmanVCTreeNF_ker_le_of_schreier`).  Take
  `r ∈ ker` with `mk r ∈ G_n`.  The action factors through `E`, so `mk r` fixes the base point
  `x₀`.  Telescoping then gives `c x₀ * mk r * c x₀⁻¹ ∈ U`, and `c x₀ ∈ U` gives `mk r ∈ U`.
  Faithfulness of `U` gives `r ∈ K`.

**Gap: `HigmanVCTreeNFSchreierStatement`.**  For arbitrarily large `n` we need three things:
* a pivot `(a, b)` of lengths `(n, n + 1)`, as in `HigmanVCTreeLevelStatement`;
* a right `Q`-set `X` whose action factors through `E` (so it is really a `V_d`-set);
* a base point `x₀` and a transversal `c : X → Q` with `c x₀ ∈ U` such that every
  **generator** of `G_n` (a balanced letter of length `n + 1`, or the single pivot `(a, b)`) has
  every Schreier element in `U`.

* **LOUD: it is equivalent to (1) as a Prop** (`higmanVCTreeNF_schreier_of_ker_le` in
  `EnvelopeHigmanVCTreeNFConverse`).  Every true Prop is.  It is NOT strictly weaker as a Prop.
  Under (1) the witness is trivial: `X = Q`, `c = id`.  That witness is not usable as a
  proof strategy.
* **Smaller in proof content.**  Relative to `HigmanVCTreeLevelStatement`, the quantifier over
  all kernel words `r` with class in `G_n` is gone.  So are the word induction and the
  faithfulness of the balanced part; both are discharged here.  What is left is *construct* `c`,
  then *check* one letter at a time on a finite alphabet (`d^{2(n+1)}` balanced letters plus one
  pivot), and all of that happens in `Q`.
* **Intended witness (not supplied).**  Let `X` be the set of cosets of `E(U)` in `V_d`, i.e.
  the local-defect (δ) profiles, acted on through `E`.  Let `c` be a canonical tree-pair word
  for each profile, built from pivot-type letters.  Then a balanced letter changes no profile
  and should conjugate `c x` into `U` by the split/deep relators.  The pivot changes one
  profile entry by `±1` along one branch.
* **Avoids** the single-antichain route, `HigmanVCTauConjShortStatement`, `HigmanVCShortComplete`,
  `HigmanVCTFPShortCompleteStatement`, `CentralBalanced` and `AllAntichain`, and letter-by-letter
  reduction of the kernel word.  The one-letter checks are about Schreier elements, not about
  eliminating letters from `r`.
* **Truth.**  The Statement holds iff (1) does.  `scratchpad/bh-met-77l/check.py` tests the
  proved parts (the telescoping identity and the base-point argument) on concrete finite
  permutation models.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The evaluation `Q →* V_d`: the relators are in the kernel. -/
noncomputable def higmanVCTreeNF_E (d : ℕ) : higmanVCCommon_Q d →* ↥(higmanThompsonV (Fin d)) :=
  QuotientGroup.lift (Subgroup.normalClosure (higmanVC_rels d fun _ => True)) (higmanVC_evalAll d)
    (Subgroup.normalClosure_le_normal (higmanVC_rels_subset_ker d fun _ => True))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_E

theorem higmanVCTreeNF_E_mk (d : ℕ) (r : FreeGroup (List (Fin d) × List (Fin d))) :
    higmanVCTreeNF_E d (higmanVCCommon_mk d r) = higmanVC_evalAll d r :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_E_mk

/-- The subgroup of elements all of whose Schreier elements `c x * q * c (x • q)⁻¹` lie in
`U`. -/
def higmanVCTreeNF_schreierSub {G X : Type*} [Group G] (U : Subgroup G) (act : X → G → X)
    (c : X → G) (h1 : ∀ x, act x 1 = x) (hm : ∀ x q q', act x (q * q') = act (act x q) q') :
    Subgroup G where
  carrier := {q | ∀ x, c x * q * (c (act x q))⁻¹ ∈ U}
  mul_mem' := fun {a b} ha hb x => by
    have e : c x * (a * b) * (c (act x (a * b)))⁻¹ =
        (c x * a * (c (act x a))⁻¹) * (c (act x a) * b * (c (act (act x a) b))⁻¹) := by
      rw [hm]
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [e]
    exact U.mul_mem (ha x) (hb (act x a))
  one_mem' := fun x => by
    rw [h1, mul_one, mul_inv_cancel]
    exact U.one_mem
  inv_mem' := fun {a} ha x => by
    have h0 := ha (act x a⁻¹)
    rw [← hm, inv_mul_cancel, h1] at h0
    have e : c x * a⁻¹ * (c (act x a⁻¹))⁻¹ = (c (act x a⁻¹) * a * (c x)⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [e]
    exact U.inv_mem h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_schreierSub

theorem higmanVCTreeNF_mem_schreierSub {G X : Type*} [Group G] {U : Subgroup G}
    {act : X → G → X} {c : X → G} {h1 : ∀ x, act x 1 = x}
    {hm : ∀ x q q', act x (q * q') = act (act x q) q'} {q : G} :
    q ∈ higmanVCTreeNF_schreierSub U act c h1 hm ↔ ∀ x, c x * q * (c (act x q))⁻¹ ∈ U :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_mem_schreierSub

/-- **Schreier telescoping.**  If every generator has all its Schreier elements in `U`, so does
every element of the generated subgroup. -/
theorem higmanVCTreeNF_telescope {G X : Type*} [Group G] (U : Subgroup G) (act : X → G → X)
    (c : X → G) (h1 : ∀ x, act x 1 = x) (hm : ∀ x q q', act x (q * q') = act (act x q) q')
    (S : Set G) (hS : ∀ g ∈ S, ∀ x, c x * g * (c (act x g))⁻¹ ∈ U) :
    ∀ q ∈ Subgroup.closure S, ∀ x, c x * q * (c (act x q))⁻¹ ∈ U := by
  have hT : Subgroup.closure S ≤ higmanVCTreeNF_schreierSub U act c h1 hm :=
    (Subgroup.closure_le _).mpr fun g hg => higmanVCTreeNF_mem_schreierSub.mpr (hS g hg)
  intro q hq
  exact higmanVCTreeNF_mem_schreierSub.mp (hT hq)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_telescope

/-- **The remaining gap: a Schreier transversal for `G_n` modulo the balanced subgroup.**

For arbitrarily large `n` we need all of the following:
* a pivot `(a, b)` of lengths `(n, n + 1)`;
* a right `Q`-set `X` (`act`) whose action factors through `E : Q → V_d`;
* a base point `x₀` and a transversal `c : X → Q` with `c x₀ ∈ U`,

such that every generator `g` of `G_n` and every `x : X` satisfy
`c x * g * (c (x • g))⁻¹ ∈ U`.

LOUD: this is Prop-equivalent to (1), as is every true Prop
(`higmanVCTreeNF_schreier_of_ker_le`). -/
def HigmanVCTreeNFSchreierStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧
    ∃ (X : Type) (act : X → higmanVCCommon_Q d → X) (x₀ : X) (c : X → higmanVCCommon_Q d),
      (∀ x, act x 1 = x) ∧ (∀ x q q', act x (q * q') = act (act x q) q') ∧
      (∀ x q q', higmanVCTreeNF_E d q = higmanVCTreeNF_E d q' → act x q = act x q') ∧
      c x₀ ∈ higmanVCTreeNF_U d ∧
      ∀ g ∈ higmanVCTreeLevel_gens d n a b, ∀ x,
        c x * g * (c (act x g))⁻¹ ∈ higmanVCTreeNF_U d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTreeNFSchreierStatement

/-- **Reduction (proved):** the Schreier gap gives the level gap. -/
theorem higmanVCTreeNF_level_of_schreier (h : HigmanVCTreeNFSchreierStatement) :
    HigmanVCTreeLevelStatement := by
  intro d hd N
  obtain ⟨n, hN, a, b, ha, hb, hab, hba, X, act, x₀, c, h1, hm, hE, hc₀, hS⟩ := h d hd N
  refine ⟨n, hN, a, b, ha, hb, hab, hba, fun r hr hG => ?_⟩
  have hfix : act x₀ (higmanVCCommon_mk d r) = x₀ := by
    rw [hE x₀ (higmanVCCommon_mk d r) 1
      (by rw [higmanVCTreeNF_E_mk, map_one]; exact MonoidHom.mem_ker.mp hr), h1]
  have ht := higmanVCTreeNF_telescope (higmanVCTreeNF_U d) act c h1 hm
    (higmanVCTreeLevel_gens d n a b) hS (higmanVCCommon_mk d r) hG x₀
  rw [hfix] at ht
  exact higmanVCTreeNF_U_faithful (by omega) hr (higmanVCTreeLevel_mem_of_conj hc₀ ht rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_level_of_schreier

/-- **Endpoint:** the Schreier gap gives (1). -/
theorem higmanVCTreeNF_ker_le_of_schreier (h : HigmanVCTreeNFSchreierStatement) (d : ℕ)
    (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  higmanVCTreeLevel_ker_le_of_level (higmanVCTreeNF_level_of_schreier h) d hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_ker_le_of_schreier

end GroupApproximation.BooneHigman.Metabelian.Envelope
