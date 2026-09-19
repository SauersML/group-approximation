import GroupApproximation.Sofic.SoficActionCyclicExtension
import GroupApproximation.Sofic.SoficActionFiniteOrbits
import GroupApproximation.Sofic.MappingTelescopeFiniteOrbits

/-!
# The finite-index ascending-HNN coset action is sofic

**Theorem 13.5** of the dossier.  If the compressing endomorphism has
finite-index image, then the coset action of the ascending HNN extension on
`G/Γ` is sofic.  No soficity or residual finiteness hypothesis on `Γ` is needed:
finite index alone makes every telescope level act with finite orbits, and
action soficity does not require the acting group to admit a free finite model.

Whether this action is sofic when the base is sofic or residually finite is a
question of Francesco Fournier-Facio.  The theorem below answers it for
finite-index image, and `isSoficAction_vertical_cosets_of_uas` answers it for
arbitrary self-embeddings over a universally action-sofic base; the general
residually finite case is open.

The proof is the two permanence lemmas applied in turn.

* Each telescope level is commensurable with the base, hence has finite orbits
  on the coset space (`MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit`),
  and every finite subset of the telescope sits inside one level.  So
  `isSoficAction_of_locally_finite_orbits` makes the telescope act soficly, with
  exact models at every window.
* The vertical group is the telescope extended by the shift, so
  `isSoficAction_semidirect` adjoins the stable-letter direction.
-/

namespace GroupApproximation
namespace MarkedCompression

open MappingTelescope MappingTelescopeFiniteOrbits SemidirectProduct CyclicStack

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The telescope acts on the coset space through the vertical group. -/
local instance telescopeCosetAction : MulAction (Telescope α hα) (Cosets α hα) :=
  MulAction.compHom _ (inl : Telescope α hα →* Vertical α hα)

@[simp] theorem telescope_smul_cosets (g : Telescope α hα) (x : Cosets α hα) :
    g • x = (inl g : Vertical α hα) • x := rfl

include hα in
/-- Any finite subset of the telescope lies at a single level. -/
theorem exists_common_level_finset (F : Finset (Telescope α hα)) :
    ∃ n : ℕ, ∀ g ∈ F, g ∈ (level α hα n).range := by
  classical
  choose lvl elt hrepr using exists_level_repr α hα
  refine ⟨F.sup lvl, fun g hg => ?_⟩
  have hg' := hrepr g
  rw [← hg']
  exact level_mem_range_of_le α hα (Finset.le_sup hg) (elt g)

include hα in
/-- **Lemma 13.2, in orbit form.**  Every telescope level has finite orbits on
the coset space. -/
theorem subgroupOrbit_level_finite [α.range.FiniteIndex] (n : ℕ)
    (x : Cosets α hα) :
    (subgroupOrbit ((level α hα n).range) x).Finite := by
  refine Set.Finite.subset (finite_verticalLevel_orbit α hα n x) ?_
  rintro y ⟨g, hg, rfl⟩
  obtain ⟨z, rfl⟩ := hg
  exact ⟨⟨inl (level α hα n z), ⟨z, rfl⟩⟩, rfl⟩

include hα in
/-- The telescope acts soficly on the coset space, with exact models. -/
theorem isSoficAction_telescope_cosets [α.range.FiniteIndex] :
    IsSoficAction (Telescope α hα) (Cosets α hα) := by
  classical
  haveI : DecidableEq (Cosets α hα) := Classical.decEq _
  refine isSoficAction_of_locally_finite_orbits ?_
  intro F
  obtain ⟨n, hn⟩ := exists_common_level_finset α hα F
  exact ⟨(level α hα n).range, hn, subgroupOrbit_level_finite α hα n⟩

include hα in
/-- **Theorem 13.5.**  The coset action of the ascending HNN extension along a
proper self-embedding with finite-index image is sofic. -/
theorem isSoficAction_vertical_cosets [α.range.FiniteIndex] :
    IsSoficAction (Vertical α hα) (Cosets α hα) := by
  classical
  haveI : DecidableEq (Cosets α hα) := Classical.decEq _
  exact isSoficAction_semidirect (fun _ _ => rfl)
    (isSoficAction_telescope_cosets α hα)


/-! ## Arbitrary self-embeddings over a universally action-sofic base -/

/-- **Definition 31.1.**  A group is *universally action-sofic* when every one
of its actions on a set is sofic.  LERF and more generally LERA groups have this
property (Gao); the point of the definition is that it is exactly what the
telescope argument consumes. -/
def UniversallyActionSofic (Γ : Type u) [Group Γ] : Prop :=
  ∀ (Y : Type u) [MulAction Γ Y], IsSoficAction Γ Y

include hα in
/-- **Theorem 31.2.**  Over a universally action-sofic base the ascending-HNN
coset action is sofic for an **arbitrary** injective self-embedding, with no
finite-index hypothesis.  Each telescope level is a copy of the base, hence acts
soficly; the levels exhaust the telescope; and the shift direction is adjoined
by the cyclic extension theorem. -/
theorem isSoficAction_vertical_cosets_of_uas
    (hUAS : UniversallyActionSofic Γ) :
    IsSoficAction (Vertical α hα) (Cosets α hα) := by
  classical
  haveI : DecidableEq (Cosets α hα) := Classical.decEq _
  have hTel : IsSoficAction (Telescope α hα) (Cosets α hα) := by
    refine isSoficAction_of_subgroup_cover ?_
    intro F
    obtain ⟨n, hn⟩ := exists_common_level_finset α hα F
    refine ⟨(level α hα n).range, hn, ?_⟩
    letI : MulAction Γ (Cosets α hα) :=
      MulAction.compHom _
        ((inl : Telescope α hα →* Vertical α hα).comp (level α hα n))
    exact IsSoficAction.of_mulEquiv
      (MonoidHom.ofInjective (level_injective α hα n)) (fun _ _ => rfl)
      (hUAS (Cosets α hα))
  exact isSoficAction_semidirect (fun _ _ => rfl) hTel

end MarkedCompression
end GroupApproximation
