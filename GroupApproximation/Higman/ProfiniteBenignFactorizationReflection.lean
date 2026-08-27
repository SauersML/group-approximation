import GroupApproximation.Higman.ProfiniteBenignProductSeparable

/-!
# Prescribed finite-quotient reflection at a benign cutter

Product separation detects that no factorization exists.  The synchronized
Inf step needs a stronger relative statement: after prescribing a finite
quotient of the source, choose one finite quotient of the witness ambient in
which every source element that collides with the cutter already lies in the
prescribed image of the cut-out source subgroup.
-/

namespace GroupApproximation
namespace Higman

noncomputable section

variable {G N : Type} [Group G] [Group N]

/-- Uniform, prescribed-quotient reflection of source--cutter collisions. -/
def ProfiniteBenignWitness.FactorizationReflecting {H : Subgroup G}
    (u : ProfiniteBenignWitness H) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (q : G →* Q),
    ∃ (R : Type) (_ : Group R) (_ : Finite R) (p : u.witness.K →* R),
      ∀ g : G, p (u.witness.emb g) ∈ u.witness.L.map p →
        q g ∈ H.map q

namespace ProfiniteBenignWitness.FactorizationReflecting

/-- Coordinate form of reflection through the direct-product comap witness.
It reflects a prescribed quotient of the target coordinate `N`; this is the
exact form used by hprod, where `phi` is first projection. -/
theorem comap_coordinate
    {H : Subgroup N} (u : ProfiniteBenignWitness H)
    (hu : u.FactorizationReflecting)
    (v : ProfiniteFPOvergroup G) (phi : G →* N)
    (Q : Type) [Group Q] [Finite Q] (q : N →* Q) :
    ∃ (R : Type) (_ : Group R) (_ : Finite R)
        (p : (ProfiniteBenignWitness.comap v phi u).witness.K →* R),
      ∀ g : G,
        p ((ProfiniteBenignWitness.comap v phi u).witness.emb g) ∈
            (ProfiniteBenignWitness.comap v phi u).witness.L.map p →
          q (phi g) ∈ H.map q := by
  obtain ⟨R, hRgroup, hRfinite, p, hp⟩ := hu Q q
  refine ⟨R, hRgroup, hRfinite,
    p.comp (MonoidHom.snd v.overgroup.K u.witness.K), ?_⟩
  intro g hg
  obtain ⟨l, hl, hleq⟩ := Subgroup.mem_map.mp hg
  have hl₂ : l.2 ∈ u.witness.L := (Subgroup.mem_prod.mp hl).2
  apply hp (phi g)
  refine ⟨l.2, hl₂, ?_⟩
  exact hleq

end ProfiniteBenignWitness.FactorizationReflecting

end

end Higman
end GroupApproximation
