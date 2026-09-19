import GroupApproximation.Algebra.TorsionFreeRadical

/-!
# The universal torsion-free quotient

Chiodo, arXiv:1107.1489v4, Corollary 3.4: every group `G` has a torsion-free
quotient `G^tf` through which every homomorphism from `G` to a torsion-free
group factors, uniquely.  `Algebra.TorsionFreeRadical` proves the two facts
this rests on --- the radical is normal, and it is contained in the kernel of
any map to a torsion-free group --- so this file is the packaging: the
quotient, the projection, the lift, and the uniqueness of the lift.

Two consequences are what the rest of the development actually consumes.

* `toTorsionFreeQuotient_injective` --- a torsion-free group is its own
  torsion-free quotient, so passing to `G^tf` costs nothing when `G` was
  already torsion-free.
* `injective_of_retraction` --- **the retraction principle**.  If a
  torsion-free `K` sits inside `G` as a *retract*, then `K` still sits inside
  `G^tf`.  The proof is one application of the universal property to the
  retraction `r : G →* K`: `r` kills the radical because `K` is torsion-free,
  so nothing of `K` can be killed by the projection.

  This is what makes the construction in
  `Monsters.ChiodoTorsionFreeAbsorber` work, and it is why that construction
  can afford to take a restricted direct product over *every* finite
  presentation, torsion-free or not: coordinates of a direct product are
  retracts, so the torsion-free coordinates survive the passage to the
  torsion-free quotient no matter what the other coordinates do.  No
  filtering of the index set is needed, and no filtering is possible --- see
  that file for why the filtered index set was the obstruction.
-/

namespace GroupApproximation
namespace Chiodo

universe u v w

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-! ## 1.  The quotient and the projection -/

/-- **`G^tf`**, Chiodo's universal torsion-free quotient. -/
abbrev TorsionFreeQuotient (G : Type u) [Group G] : Type u :=
  G ⧸ torsionFreeRadical G

/-- The projection `G → G^tf`. -/
def toTorsionFreeQuotient (G : Type u) [Group G] : G →* TorsionFreeQuotient G :=
  QuotientGroup.mk' (torsionFreeRadical G)

theorem toTorsionFreeQuotient_surjective :
    Function.Surjective (toTorsionFreeQuotient G) :=
  QuotientGroup.mk'_surjective _

theorem ker_toTorsionFreeQuotient :
    MonoidHom.ker (toTorsionFreeQuotient G) = torsionFreeRadical G :=
  QuotientGroup.ker_mk' _

/-- **Corollary 3.4, first half.** -/
theorem isPowerTorsionFree_torsionFreeQuotient :
    IsPowerTorsionFree (TorsionFreeQuotient G) :=
  isPowerTorsionFree_quotient_torsionFreeRadical

theorem toTorsionFreeQuotient_eq_one_iff {g : G} :
    toTorsionFreeQuotient G g = 1 ↔ g ∈ torsionFreeRadical G := by
  constructor
  · intro h
    have hk : g ∈ MonoidHom.ker (toTorsionFreeQuotient G) :=
      MonoidHom.mem_ker.mpr h
    rwa [ker_toTorsionFreeQuotient] at hk
  · intro h
    have hk : g ∈ MonoidHom.ker (toTorsionFreeQuotient G) := by
      rwa [ker_toTorsionFreeQuotient]
    exact MonoidHom.mem_ker.mp hk

/-! ## 2.  The universal property -/

/-- **Corollary 3.4, second half.**  The factorization of a homomorphism into
a torsion-free group through `G^tf`. -/
def liftTorsionFree (f : G →* H) (hH : IsPowerTorsionFree H) :
    TorsionFreeQuotient G →* H :=
  QuotientGroup.lift (torsionFreeRadical G) f (torsionFreeRadical_le_ker f hH)

@[simp] theorem liftTorsionFree_apply (f : G →* H) (hH : IsPowerTorsionFree H)
    (g : G) : liftTorsionFree f hH (toTorsionFreeQuotient G g) = f g :=
  rfl

theorem liftTorsionFree_comp (f : G →* H) (hH : IsPowerTorsionFree H) :
    (liftTorsionFree f hH).comp (toTorsionFreeQuotient G) = f := by
  ext g
  show liftTorsionFree f hH (toTorsionFreeQuotient G g) = f g
  exact liftTorsionFree_apply f hH g

/-- Two homomorphisms out of `G^tf` agreeing on the image of `G` are equal;
the projection is onto. -/
theorem torsionFreeQuotient_hom_ext {φ ψ : TorsionFreeQuotient G →* H}
    (h : φ.comp (toTorsionFreeQuotient G) = ψ.comp (toTorsionFreeQuotient G)) :
    φ = ψ := by
  -- `ext` descends through the quotient on its own, so the element is
  -- already a representative and no surjectivity step is needed.
  ext x
  have hg := congrArg (fun θ : G →* H => θ x) h
  exact hg

/-- **Uniqueness of the factorization**, the clause Chiodo records on page 4:
the projection is surjective, so the factoring map is unique. -/
theorem liftTorsionFree_unique (f : G →* H) (hH : IsPowerTorsionFree H)
    (φ : TorsionFreeQuotient G →* H)
    (hφ : φ.comp (toTorsionFreeQuotient G) = f) : φ = liftTorsionFree f hH := by
  refine torsionFreeQuotient_hom_ext ?_
  rw [hφ, liftTorsionFree_comp]

/-! ## 3.  What the construction consumes -/

/-- A torsion-free group is its own torsion-free quotient: the projection is
injective. -/
theorem toTorsionFreeQuotient_injective (hG : IsPowerTorsionFree G) :
    Function.Injective (toTorsionFreeQuotient G) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  rw [ker_toTorsionFreeQuotient]
  exact torsionFreeRadical_eq_bot_iff.mpr hG

/-- **The retraction principle.**  A torsion-free retract of `G` embeds in
`G^tf`.

Only the retraction `r` is used, and only through the universal property:
`r` maps to a torsion-free group, so it kills the radical, so no element of
the retract can be sent to `1` by the projection unless it was `1`. -/
theorem injective_of_retraction {K : Type w} [Group K] (hK : IsPowerTorsionFree K)
    (ι : K →* G) (r : G →* K) (hr : ∀ x : K, r (ι x) = x) :
    Function.Injective ((toTorsionFreeQuotient G).comp ι) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [MonoidHom.comp_apply] at hx
  have hmem : ι x ∈ torsionFreeRadical G :=
    toTorsionFreeQuotient_eq_one_iff.mp hx
  have hone : r (ι x) = 1 :=
    map_eq_one_of_mem_torsionFreeRadical r hK hmem
  rw [hr x] at hone
  exact hone

/-- The functorial action of `·^tf` on homomorphisms. -/
def mapTorsionFree (f : G →* H) : TorsionFreeQuotient G →* TorsionFreeQuotient H :=
  liftTorsionFree ((toTorsionFreeQuotient H).comp f)
    isPowerTorsionFree_torsionFreeQuotient

@[simp] theorem mapTorsionFree_apply (f : G →* H) (g : G) :
    mapTorsionFree f (toTorsionFreeQuotient G g) = toTorsionFreeQuotient H (f g) :=
  rfl

end Chiodo
end GroupApproximation
