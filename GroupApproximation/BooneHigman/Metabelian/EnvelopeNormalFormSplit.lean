import GroupApproximation.BooneHigman.Metabelian.EnvelopeNormalFormLocal
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting relators of the normal form and the full relator set

The wreath recursion `nf_wreath` gives two more families of relators in `RNFree X H`.
* `nfSplitRelators`: `(nfL h)⁻¹ * nfV a * Π_{x ∈ l} nfV (c x) * nfL (k x) * (nfV (c x))⁻¹`.
  Here `l` lists `X` without repetition, `k x` is the state of `h` at `[x]`, `c x ∈ V_X` carries
  `cone [x₀]` onto `cone [x₀, x]`, and `a = localize [x₀] (nfRootShift (rootPerm h))`.
* `nfRootRelators`: the same with `nfH h`, `c x` carrying `cone [x₀]` onto `cone [x]`, and
  `a = nfRootShift (rootPerm h)`.

Route.  `nf_prod_conj_eq`: the product maps to `localize u (nfLevelProd l (state h))`, where
`u = [x₀]` or `u = []`.  Each factor is `localize (u ++ [x]) (h|_x)` by
`MapsCone.conj_localize`, which is `localize u (localize [x] (h|_x))` by `localize_append`.
Then `nf_wreath` turns `nfRootShift (rootPerm h) * nfLevelProd l (state h)` into `h`.

`nfRelators` is the union of the four families, and `nfRelators_subset_ker` puts it in the kernel.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X]

theorem nf_prod_conj_eq (H : Subgroup (TreeAut X)) (x₀ : X) (h : ↥H)
    (c : X → ↥(higmanThompsonV X)) (k : X → ↥H) (l u : List X)
    (hk : ∀ x, (k x : TreeAut X) = TreeAut.state (h : TreeAut X) [x])
    (hc : ∀ x, MapsCone (c x : Equiv.Perm (Cantor X)) [x₀] (u ++ [x])) :
    rnFreeToPerm H x₀ (l.map fun x => nfV H (c x) * nfL H (k x) * (nfV H (c x))⁻¹).prod =
      localize u (nfLevelProd l fun x => cantorHom (TreeAut.state (h : TreeAut X) [x])) := by
  rw [map_list_prod (rnFreeToPerm H x₀), List.map_map, nfLevelProd, map_list_prod (localize u),
    List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, map_mul, map_inv, nf_toPerm_V, nf_toPerm_L, hk]
  rw [(hc x).conj_localize, localize_append]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nf_prod_conj_eq

/-- **Splitting relators.**  `localize [x₀] h` is a shift in `V_X` times the product of the
states of `h` localised at the cones `[x₀, x]`. -/
def nfSplitRelators (H : Subgroup (TreeAut X)) (x₀ : X) : Set (RNFree X H) :=
  {r | ∃ (h : ↥H) (a : ↥(higmanThompsonV X)) (c : X → ↥(higmanThompsonV X)) (k : X → ↥H)
    (l : List X), l.Nodup ∧ (∀ x, x ∈ l) ∧
      (∀ x, (k x : TreeAut X) = TreeAut.state (h : TreeAut X) [x]) ∧
      (∀ x, MapsCone (c x : Equiv.Perm (Cantor X)) [x₀] [x₀, x]) ∧
      (a : Equiv.Perm (Cantor X)) = localize [x₀] (nfRootShift (TreeAut.rootPerm (h : TreeAut X))) ∧
      r = (nfL H h)⁻¹ * nfV H a *
        (l.map fun x => nfV H (c x) * nfL H (k x) * (nfV H (c x))⁻¹).prod}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfSplitRelators

theorem nfSplitRelators_subset_ker (H : Subgroup (TreeAut X)) (x₀ : X) :
    nfSplitRelators H x₀ ⊆ (rnFreeHom H x₀).ker := by
  rintro r ⟨h, a, c, k, l, hl, hall, hk, hc, ha, rfl⟩
  rw [nf_mem_ker_iff, map_mul, map_mul, map_inv, nf_toPerm_V, nf_toPerm_L, ha,
    nf_prod_conj_eq H x₀ h c k l [x₀] hk hc, mul_assoc, ← map_mul,
    ← nf_wreath (h : TreeAut X) l hl hall, inv_mul_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfSplitRelators_subset_ker

/-- **Root relators.**  The global copy `h` is a shift in `V_X` times the product of the states
of `h` localised at the cones `[x]`. -/
def nfRootRelators (H : Subgroup (TreeAut X)) (x₀ : X) : Set (RNFree X H) :=
  {r | ∃ (h : ↥H) (a : ↥(higmanThompsonV X)) (c : X → ↥(higmanThompsonV X)) (k : X → ↥H)
    (l : List X), l.Nodup ∧ (∀ x, x ∈ l) ∧
      (∀ x, (k x : TreeAut X) = TreeAut.state (h : TreeAut X) [x]) ∧
      (∀ x, MapsCone (c x : Equiv.Perm (Cantor X)) [x₀] [x]) ∧
      (a : Equiv.Perm (Cantor X)) = nfRootShift (TreeAut.rootPerm (h : TreeAut X)) ∧
      r = (nfH H h)⁻¹ * nfV H a *
        (l.map fun x => nfV H (c x) * nfL H (k x) * (nfV H (c x))⁻¹).prod}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfRootRelators

theorem nfRootRelators_subset_ker (H : Subgroup (TreeAut X)) (x₀ : X) :
    nfRootRelators H x₀ ⊆ (rnFreeHom H x₀).ker := by
  rintro r ⟨h, a, c, k, l, hl, hall, hk, hc, ha, rfl⟩
  rw [nf_mem_ker_iff, map_mul, map_mul, map_inv, nf_toPerm_V, nf_toPerm_H, ha,
    nf_prod_conj_eq H x₀ h c k l [] hk hc, localize_nil, mul_assoc,
    ← nf_wreath (h : TreeAut X) l hl hall, inv_mul_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfRootRelators_subset_ker

/-- The four relator families of the normal form. -/
def nfRelators (H : Subgroup (TreeAut X)) (x₀ : X) : Set (RNFree X H) :=
  nfCommRelators H x₀ ∪ nfDisjRelators H x₀ ∪ nfSplitRelators H x₀ ∪ nfRootRelators H x₀

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfRelators

theorem nfRelators_subset_ker (H : Subgroup (TreeAut X)) (x₀ : X) :
    nfRelators H x₀ ⊆ (rnFreeHom H x₀).ker :=
  Set.union_subset
    (Set.union_subset
      (Set.union_subset (nfCommRelators_subset_ker H x₀) (nfDisjRelators_subset_ker H x₀))
      (nfSplitRelators_subset_ker H x₀))
    (nfRootRelators_subset_ker H x₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.nfRelators_subset_ker

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
