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

/-- Reflection of source--cutter collisions for one prescribed finite source
quotient.  Keeping the quotient visible is essential at an Inf step: a
comap witness generally reflects only quotients factoring through the comap
map, rather than every quotient of its enlarged source. -/
def ProfiniteBenignWitness.FactorizationReflectingAt {H : Subgroup G}
    (u : ProfiniteBenignWitness H) (Q : Type) [Group Q] [Finite Q]
    (q : G →* Q) : Prop :=
  ∃ (R : Type) (_ : Group R) (_ : Finite R) (p : u.witness.K →* R),
    ∀ g : G, p (u.witness.emb g) ∈ u.witness.L.map p →
      q g ∈ H.map q

/-- Uniform prescribed-quotient reflection. -/
def ProfiniteBenignWitness.FactorizationReflecting {H : Subgroup G}
    (u : ProfiniteBenignWitness H) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (q : G →* Q),
    u.FactorizationReflectingAt Q q

namespace ProfiniteBenignWitness.FactorizationReflecting

/-- A retraction which sends the cutter back into the cut-out subgroup gives
prescribed reflection by postcomposing the requested source quotient. -/
theorem of_retraction
    {H : Subgroup G} (u : ProfiniteBenignWitness H)
    (r : u.witness.K →* G)
    (hrt : r.comp u.witness.emb = MonoidHom.id G)
    (hrL : u.witness.L.map r ≤ H) :
    u.FactorizationReflecting := by
  intro Q _ _ q
  refine ⟨Q, inferInstance, inferInstance, q.comp r, ?_⟩
  intro g hg
  obtain ⟨l, hl, hleq⟩ := Subgroup.mem_map.mp hg
  have hrg : r (u.witness.emb g) = g := by
    have h := DFunLike.congr_fun hrt g
    exact h
  refine ⟨r l, hrL ⟨l, hl, rfl⟩, ?_⟩
  rw [← hrg]
  exact hleq

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

/-- Named `At` form of coordinate reflection, convenient when assembling a
synchronized Inf quotient. -/
theorem comap_coordinate_at
    {H : Subgroup N} (u : ProfiniteBenignWitness H)
    (hu : u.FactorizationReflecting)
    (v : ProfiniteFPOvergroup G) (phi : G →* N)
    (hphi : Function.Surjective phi)
    (Q : Type) [Group Q] [Finite Q] (q : N →* Q) :
    (ProfiniteBenignWitness.comap v phi u).FactorizationReflectingAt Q
      (q.comp phi) := by
  obtain ⟨R, hRgroup, hRfinite, p, hp⟩ :=
    comap_coordinate u hu v phi Q q
  refine ⟨R, hRgroup, hRfinite, p, ?_⟩
  intro g hg
  obtain ⟨n, hn, hneq⟩ := Subgroup.mem_map.mp (hp g hg)
  obtain ⟨g', rfl⟩ := hphi n
  refine ⟨g', Subgroup.mem_comap.mpr hn, ?_⟩
  exact hneq

end ProfiniteBenignWitness.FactorizationReflecting

end

end Higman
end GroupApproximation
