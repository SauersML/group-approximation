import GroupApproximation.Criterion.ChainConditionCompression

/-!
# Compression cannot shrink a chain-condition envelope: the abstract core

The manuscript takes the invariant of a subgroup to be the Zariski closure
of its image in `GL(V)` and observes that, since the closed subgroups of
an algebraic group satisfy the descending chain condition, a one-sided
compression assigns the compressed subgroup and the subgroup the same
algebraic envelope.

What is proved here is that the deduction needs nothing about algebraic
geometry: any conjugation-stable notion of "closed" whose closed subgroups
satisfy the descending chain condition forces the same conclusion.
Conjugation by a fixed element is an order isomorphism of that poset, and an
order isomorphism moving a point down in a poset with no infinite descending
chain fixes it --- which is `ChainConditionCompression`.

## Why this file exists separately

The badged declaration `ClosedEnvelopeCompression.manuscriptEnvelopeCompressionBlind`
lives in `Criterion/ClosedEnvelopeCompression`, and it states the Zariski
instance as well as the abstract principle --- because the manuscript's
`rem:chaincondition` prints both, and a badge on the abstract half alone would
certify a true statement that is not the printed one.  Stating the instance
means that file has to sit *downstream* of `Algebra/ZariskiEnvelopeEndpoint`,
which in turn needs the abstract theorem.  So the abstract theorem lives here,
one level up, and everything keeps the namespace `ClosedEnvelopeCompression`:
callers write `ClosedEnvelopeCompression.envelope_conj_eq` exactly as before,
and only the `import` line moves.

The chain condition itself enters here as a single instance argument,
`WellFoundedLT {H // Closed H}`.  **That instance is not an external input.**
`Algebra/ZariskiDescendingChain` builds the Zariski topology on `GL n k` for
an arbitrary field, proves `wellFoundedLT_isZClosedSubgroup` from the Hilbert
basis theorem, and `Algebra/ZariskiEnvelopeEndpoint` exhibits the whole
package at it.  Nothing in the chain is quoted.
-/

namespace GroupApproximation
namespace ClosedEnvelopeCompression

variable {G : Type*} [Group G]

/-- Conjugation is compatible with composition of subgroup maps. -/
theorem conj_comp_conj_inv (g : G) :
    ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
      MonoidHom.id G := by
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

theorem conj_inv_comp_conj (g : G) :
    ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) =
      MonoidHom.id G := by
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

variable (Closed : Subgroup G → Prop)
  (hconj : ∀ (g : G) (H : Subgroup G), Closed H →
    Closed (H.map (MulAut.conj g).toMonoidHom))

/-- Conjugation by a fixed element is an order isomorphism of the poset of
closed subgroups. -/
def conjClosedIso (g : G) :
    {H : Subgroup G // Closed H} ≃o {H : Subgroup G // Closed H} where
  toFun H := ⟨H.1.map (MulAut.conj g).toMonoidHom, hconj g H.1 H.2⟩
  invFun H := ⟨H.1.map (MulAut.conj g⁻¹).toMonoidHom, hconj g⁻¹ H.1 H.2⟩
  left_inv H := by
    refine Subtype.ext ?_
    show (H.1.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = H.1
    rw [Subgroup.map_map, conj_comp_conj_inv, Subgroup.map_id]
  right_inv H := by
    refine Subtype.ext ?_
    show (H.1.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = H.1
    rw [Subgroup.map_map, conj_inv_comp_conj, Subgroup.map_id]
  map_rel_iff' := by
    intro H K
    show H.1.map (MulAut.conj g).toMonoidHom ≤
      K.1.map (MulAut.conj g).toMonoidHom ↔ H.1 ≤ K.1
    constructor
    · intro hle
      have hmap : (H.1.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj g⁻¹).toMonoidHom ≤
          (K.1.map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono hle
      rwa [Subgroup.map_map, conj_comp_conj_inv, Subgroup.map_id,
        Subgroup.map_map, conj_comp_conj_inv, Subgroup.map_id] at hmap
    · intro hle
      exact Subgroup.map_mono hle

include hconj in
/-- **The envelope is compression-blind.**  If the closed subgroups satisfy
the descending chain condition, a closed subgroup carried into itself by
conjugation is carried *onto* itself. -/
theorem conj_eq_of_conj_le [WellFoundedLT {H : Subgroup G // Closed H}]
    {K : Subgroup G} (hK : Closed K) {t : G}
    (ht : K.map (MulAut.conj t).toMonoidHom ≤ K) :
    K.map (MulAut.conj t).toMonoidHom = K := by
  have h := orderIso_apply_eq_self_of_apply_le (conjClosedIso Closed hconj t)
    (a := ⟨K, hK⟩) ht
  exact congrArg Subtype.val h

include hconj in
/-- The manuscript's envelope statement.  `envelope` is any conjugation-
equivariant closure operator landing in the closed subgroups --- the
Zariski closure is the intended instance --- and the conclusion is that a
compressed subgroup has the same envelope as the subgroup. -/
theorem envelope_conj_eq [WellFoundedLT {H : Subgroup G // Closed H}]
    (envelope : Subgroup G → Subgroup G)
    (hclosed : ∀ H, Closed (envelope H))
    (hmono : Monotone envelope)
    (hequiv : ∀ (g : G) (H : Subgroup G),
      envelope (H.map (MulAut.conj g).toMonoidHom) =
        (envelope H).map (MulAut.conj g).toMonoidHom)
    {Γ : Subgroup G} {t : G}
    (ht : Γ.map (MulAut.conj t).toMonoidHom ≤ Γ) :
    envelope (Γ.map (MulAut.conj t).toMonoidHom) = envelope Γ := by
  rw [hequiv]
  exact conj_eq_of_conj_le Closed hconj (hclosed Γ)
    (by rw [← hequiv]; exact hmono ht)

/-- The abstract deduction with every quantifier inside the proposition.
`manuscriptEnvelopeCompressionBlind` in `Criterion/ClosedEnvelopeCompression`
states this as its first conjunct, alongside the Zariski instance. -/
theorem abstractEnvelopeCompressionBlind :
    ∀ {G : Type} [Group G] (Closed : Subgroup G → Prop),
      (∀ (g : G) (H : Subgroup G), Closed H →
          Closed (H.map (MulAut.conj g).toMonoidHom)) →
        ∀ [WellFoundedLT {H : Subgroup G // Closed H}]
          (envelope : Subgroup G → Subgroup G),
          (∀ H, Closed (envelope H)) → Monotone envelope →
          (∀ (g : G) (H : Subgroup G),
            envelope (H.map (MulAut.conj g).toMonoidHom) =
              (envelope H).map (MulAut.conj g).toMonoidHom) →
          ∀ (Γ : Subgroup G) (t : G),
            Γ.map (MulAut.conj t).toMonoidHom ≤ Γ →
            envelope (Γ.map (MulAut.conj t).toMonoidHom) = envelope Γ := by
  intro G _ Closed hconj _ envelope hclosed hmono hequiv Γ t ht
  exact envelope_conj_eq Closed hconj envelope hclosed hmono hequiv ht

end ClosedEnvelopeCompression
end GroupApproximation
