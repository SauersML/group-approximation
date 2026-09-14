import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerStatement

/-!
# Simplicity through one finite simple subgroup: the interface

`simple_kazhdan_sofic_group.tex` at e80dcf20a, subsection "Simplicity" (≈ tex 179–238).  The two
halves of the printed proof meet at a commutator `k = [g,h]` lying in the matrix copy of
`M_d(F_2)`, `d = 3(2w+1)`, over a small clopen set `V`:

> Put $k=[g,h]\in N\setminus\{1\}$. … So $k-I_3=(ghg^{-1}-h)h$ and $k^{-1}-I_3=h(ghg^{-1}-h)$ lie in
> it, say $k=I_3+\psi(A)$ and $k^{-1}=I_3+\psi(B)$.

* `towerSpanOf T k w hV`: the additive span of the `ε_{ab} = e_{T^aV}u^{a-b}`, `|a|,|b| ≤ w`, over
  the fixed set `V` (printed "the span of the $\epsilon_{ab}$"; over `F_2` the additive span is the
  linear span);
* `SimplicityCommutatorWitness T`: every nontrivial normal subgroup `N` of `G = EL_3(R_X)` over `F_2`
  contains `1 ≠ k` such that, for some nonempty clopen `V` with `V ∩ T^jV = ∅` for `0 < |j| ≤ 2w`,
  every entry of `k - I_3` and of `k⁻¹ - I_3` lies in `towerSpanOf T (ZMod 2) w hV`.

The first half produces the witness (small sets, a noncommuting root `h = e_{ij}(e_V)`, the
products `fu^a e_V f'u^b ∈ {0, ε_{a,-b}}`); the second half derives `N = G` from it.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open ClopenCrossedProduct

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k]

/-- The span of the `ε_{ab} = e_{T^aV} u^{a-b}`, `|a|, |b| ≤ w`, over a fixed clopen `V`. -/
noncomputable def towerSpanOf (w : ℕ) {V : Set X} (hV : IsClopen V) :
    AddSubgroup (ClopenCrossedProduct T k) :=
  AddSubgroup.closure (Set.range fun ab : Fin (2 * w + 1) × Fin (2 * w + 1) =>
    towerE T k w hV ab.1 ab.2)

/-- **The commutator witness of the printed simplicity proof.**  Every nontrivial normal subgroup
of `EL_3(R_X)` over `F_2` contains `1 ≠ k` whose deviations `k - I_3` and `k⁻¹ - I_3` have entries in
the `ε`-span of a nonempty clopen `V` with `V ∩ T^jV = ∅` for `0 < |j| ≤ 2w`. -/
def SimplicityCommutatorWitness : Prop :=
  ∀ (N : Subgroup (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2)))), N.Normal → N ≠ ⊥ →
    ∃ (V : Set X) (hV : IsClopen V) (w : ℕ)
      (g : elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))),
      V.Nonempty ∧ LevelsDisjoint T w V ∧ g ∈ N ∧ g ≠ 1 ∧
      ∀ p q : Fin 3,
        (((g : (Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
            Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T (ZMod 2))) - 1) p q ∈
          towerSpanOf T (ZMod 2) w hV ∧
        ((((g⁻¹ : elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) :
            (Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
            Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T (ZMod 2))) - 1) p q ∈
          towerSpanOf T (ZMod 2) w hV

end SimpleKazhdanSofic
end GroupApproximation
