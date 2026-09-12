import GroupApproximation.GGT.VanKampen.PermOrbitInsert

/-!
# Inserting an edge at two map corners

The old darts remain present. Two new darts, paired by edge reversal, are
inserted into the vertex rotations at the chosen corners. The vertex set is
unchanged, the edge set gains one element, and connectedness is preserved.
These assertions also hold when both corners are the same dart.

Planarity additionally needs the face count for corners on a common face;
that is separate from the vertex and connectivity calculations here.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv
universe u

theorem CombMap.eqvGen_of_sameCycle_sigma (M : CombMap.{u})
    {x y : M.Dart} (hxy : M.sigma.SameCycle x y) : Relation.EqvGen M.Adjacent x y := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (z : M.Dart), Relation.EqvGen M.Adjacent z ((M.sigma ^ m) z) := by
    intro m
    induction m with
    | zero => intro z; exact Relation.EqvGen.refl _
    | succ m ih =>
        intro z
        rw [pow_succ, Perm.mul_apply]
        exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl)) (ih (M.sigma z))
  simpa only [hn] using hpow n x

namespace EdgeInsertion

abbrev Dart (M : CombMap.{u}) := Option (Option M.Dart)

def embed (M : CombMap.{u}) (d : M.Dart) : Dart M := some (some d)

def alphaFun (M : CombMap.{u}) : Dart M → Dart M
  | none => some none
  | some none => none
  | some (some d) => some (some (M.alpha d))

theorem alphaFun_involutive (M : CombMap.{u}) : Function.Involutive (alphaFun M) := by
  intro x
  rcases x with _ | (_ | d)
  · rfl
  · rfl
  · exact congrArg (fun d => some (some d)) (M.alpha_involutive d)

def alpha (M : CombMap.{u}) : Perm (Dart M) := (alphaFun_involutive M).toPerm (alphaFun M)

theorem alpha_fixedPointFree (M : CombMap.{u}) (d : Dart M) : alpha M d ≠ d := by
  rcases d with _ | (_ | d)
  · intro h; cases h
  · intro h; cases h
  · intro h
    exact M.alpha_fixedPointFree d (Option.some.inj (Option.some.inj h))

/-- The first new dart is `some none` at corner `a`; the second is `none`
at corner `b`. All old darts are embedded by `some ∘ some`. -/
noncomputable def toCombMap (M : CombMap.{u}) (a b : M.Dart) : CombMap.{u} where
  Dart := Dart M
  dartFintype := inferInstance
  alpha := alpha M
  sigma := PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore M.sigma a) (some b)
  alpha_involutive := alphaFun_involutive M
  alpha_fixedPointFree := alpha_fixedPointFree M

/-- Inserting the two corner darts preserves the actual vertex quotient. -/
noncomputable def vertexEquiv (M : CombMap.{u}) (a b : M.Dart) :
    (toCombMap M a b).Vertex ≃ M.Vertex :=
  (PermOrbitInsert.orbitEquiv (PermOrbitInsert.insertBefore M.sigma a) (some b)).trans
    (PermOrbitInsert.orbitEquiv M.sigma a)

theorem vertexCount_eq (M : CombMap.{u}) (a b : M.Dart) :
    (toCombMap M a b).vertexCount = M.vertexCount := Nat.card_congr (vertexEquiv M a b)

def edgeClass (M : CombMap.{u}) : Dart M → Option M.Edge
  | none => none
  | some none => none
  | some (some d) => some (M.edgeOf d)

theorem edgeClass_alpha (M : CombMap.{u}) (d : Dart M) : edgeClass M (alpha M d) = edgeClass M d := by
  rcases d with _ | (_ | d)
  · rfl
  · rfl
  · exact congrArg some (M.edgeOf_alpha d)

/-- The edge quotient gains exactly the inserted edge. -/
noncomputable def edgeEquiv (M : CombMap.{u}) (a b : M.Dart) :
    (toCombMap M a b).Edge ≃ Option M.Edge where
  toFun := Quotient.lift (edgeClass M) (by
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact congrArg (edgeClass M) hxy
    · rw [← hxy]
      exact (edgeClass_alpha M x).symm)
  invFun := fun q => match q with
    | none => (toCombMap M a b).edgeOf none
    | some q => Quotient.map (embed M) (by
        intro x y hxy
        rcases hxy with hxy | hxy
        · exact Or.inl (congrArg (embed M) hxy)
        · exact Or.inr (congrArg (embed M) hxy)) q
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    rcases x with _ | (_ | d)
    · rfl
    · exact Quotient.sound (Or.inr rfl)
    · rfl
  right_inv q := by
    cases q with
    | none => rfl
    | some q =>
        refine Quotient.inductionOn' q ?_
        intro d
        rfl

theorem edgeCount_eq (M : CombMap.{u}) (a b : M.Dart) :
    (toCombMap M a b).edgeCount = M.edgeCount + 1 := by
  change Nat.card (toCombMap M a b).Edge = Nat.card M.Edge + 1
  rw [Nat.card_congr (edgeEquiv M a b)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

theorem old_sigma_reachable (M : CombMap.{u}) (a b d : M.Dart) :
    Relation.EqvGen (toCombMap M a b).Adjacent (embed M d) (embed M (M.sigma d)) := by
  apply CombMap.eqvGen_of_sameCycle_sigma
  exact PermOrbitInsert.sameCycle_some_of_sameCycle
    (PermOrbitInsert.insertBefore M.sigma a) (some b) (PermOrbitInsert.sameCycle_old_step M.sigma a d)

/-- Every old dart walk lifts to the enlarged map. -/
theorem old_reachable (M : CombMap.{u}) (a b : M.Dart) {x y : M.Dart}
    (hxy : Relation.EqvGen M.Adjacent x y) :
    Relation.EqvGen (toCombMap M a b).Adjacent (embed M x) (embed M y) := by
  induction hxy with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · exact Relation.EqvGen.rel _ _ (Or.inl (congrArg (embed M) hxy))
      · rw [← hxy]
        exact old_sigma_reachable M a b x
  | refl x => exact Relation.EqvGen.refl _
  | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z hxy hyz ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def oldRoot (M : CombMap.{u}) (a b : M.Dart) : Dart M → M.Dart
  | none => b
  | some none => a
  | some (some d) => d

theorem reachable_oldRoot (M : CombMap.{u}) (a b : M.Dart) (d : Dart M) :
    Relation.EqvGen (toCombMap M a b).Adjacent d (embed M (oldRoot M a b d)) := by
  rcases d with _ | (_ | d)
  · apply CombMap.eqvGen_of_sameCycle_sigma
    exact PermOrbitInsert.sameCycle_none (PermOrbitInsert.insertBefore M.sigma a) (some b)
  · apply CombMap.eqvGen_of_sameCycle_sigma
    exact PermOrbitInsert.sameCycle_some_of_sameCycle (PermOrbitInsert.insertBefore M.sigma a)
      (some b) (PermOrbitInsert.sameCycle_none M.sigma a)
  · exact Relation.EqvGen.refl _

theorem connected (M : CombMap.{u}) (a b : M.Dart) (hM : M.IsConnected) :
    (toCombMap M a b).IsConnected := by
  intro x y
  exact Relation.EqvGen.trans _ _ _ (reachable_oldRoot M a b x)
    (Relation.EqvGen.trans _ _ _ (old_reachable M a b (hM _ _))
      (Relation.EqvGen.symm _ _ (reachable_oldRoot M a b y)))

end EdgeInsertion
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.vertexEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.edgeEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.vertexCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.edgeCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.connected
