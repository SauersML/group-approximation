import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraTowerPerm
import GroupApproximation.Meta.AxiomGuard

/-!
# Tower permutations, part 3: consecutive exponents

Infrastructure for census row `2e7c7d9ab149` (the key is absent from the current tex, so there
is no line number).  Lane sk-flip-04, in the lane's own shape: the levels are `T^i V` for
`i < n`, and disjointness is indexed by natural numbers `i, j < n`.

This is `towerPerm` of `InfraTowerPerm` with the exponents `k i = i`; `towerNat_disjoint`
converts the `ℕ`-indexed disjointness hypothesis into the `Fin n`-indexed one.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

variable {X : Type*} [TopologicalSpace X]

theorem towerNat_disjoint {T : X ≃ₜ X} {V : Set X} {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V)) :
    ∀ i j : Fin n, i ≠ j →
      Disjoint ((T ^ ((i : ℕ) : ℤ)) '' V) ((T ^ ((j : ℕ) : ℤ)) '' V) :=
  fun i j hij => hdisj i i.2 j j.2 fun h => hij (Fin.ext h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerNat_disjoint

/-- Permutations of the levels `T^i V` (`i < n`) of a clopen tower, as `Sym(n) →* [[T]]`. -/
noncomputable def towerPermNat (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V)) :
    Equiv.Perm (Fin n) →* topologicalFullGroup T :=
  towerPerm T V (fun i : Fin n => ((i : ℕ) : ℤ)) hV (towerNat_disjoint hdisj)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPermNat

theorem towerPermNat_level (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) (i : Fin n) {v : X} (hv : v ∈ V) :
    ((towerPermNat T V hV hdisj π : topologicalFullGroup T) : X ≃ₜ X) ((T ^ ((i : ℕ) : ℤ)) v) =
      (T ^ ((π i : ℕ) : ℤ)) v :=
  towerPerm_level T V (fun i : Fin n => ((i : ℕ) : ℤ)) hV (towerNat_disjoint hdisj) π i hv

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPermNat_level

theorem towerPermNat_supportedIn (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) :
    SupportedIn ((towerPermNat T V hV hdisj π : topologicalFullGroup T) : X ≃ₜ X)
      (⋃ i : Fin n, (T ^ ((i : ℕ) : ℤ)) '' V) :=
  towerPerm_supportedIn T V (fun i : Fin n => ((i : ℕ) : ℤ)) hV (towerNat_disjoint hdisj) π

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPermNat_supportedIn

theorem towerPermNat_injective (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (hne : V.Nonempty) : Function.Injective (towerPermNat T V hV hdisj) :=
  towerPerm_injective T V (fun i : Fin n => ((i : ℕ) : ℤ)) hV (towerNat_disjoint hdisj) hne

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPermNat_injective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
