import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRelBrown.Block
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.Setup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.EdgeStab
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVEGen.GLEqElementary

/-!
# The relative vertex section `J → Q`

This file belongs to the relative rank-four Brown criterion (Khanh, arXiv:2609.08428, Thm 5.1),
which is used on the Leavitt route to `simple_kazhdan_sofic_group.tex` l.733-735
(`sec:questions`).

Let `Ψ : St_4(L) →* Q` kill the stabilized kernel `castSuccStab (K₂(3, L))`. Write
`J = vertexStab = {g ∈ GL_4(L) | g e₃ = e₃}`. This file constructs a homomorphism
`relSection Ψ hΨ : J →* Q` that agrees with `Ψ` on the roots `x_{ij}(a)` with `j ≠ 3`.

* `stabRowToJ : stabRow 3 L →* J` is the Steinberg projection restricted to
  `St_3(L) ⋉ L³ = {castSuccStab u * rowVec v}`.
* `stabRowToJ_surjective`: every `g ∈ J` has block form `[[A, 0], [v, 1]]`. The block `A` is
  invertible, and `St_3(L) → GL_3(L)` is onto (`LVEGen.steinbergToGL_surjective`).
* `stabRowToJ_ker_le`: the kernel is `castSuccStab (K₂(3, L))` (`stabRow_ker`), so `Ψ` kills it.
* `relSection`: the induced homomorphism, `relSection_stabRowToJ`, and the relative
  `LiftsRoots` statement `relSection_elementaryUnit`.

With `Q = St_4(L)` and `Ψ = id`, this is the vertex section of `LVAssembly`
(`LVAssembly.LiftsRoots`).
-/

namespace GroupApproximation
namespace Full
namespace LVRelBrown

open SteinbergGroup ElementarySimplicity LVCentral LVAssembly

noncomputable section

/-- The Steinberg projection maps `stabRow 3 L` into `J = vertexStab`. -/
theorem projection_mem_vertexStab (g : SteinbergGroup (Fin 4) BinL) (hg : g ∈ stabRow 3 BinL) :
    ((projection g : elementaryGroup (Fin 4) BinL) : GLFour) ∈ vertexStab := by
  obtain ⟨u, v, rfl⟩ := mem_stabRow.mp hg
  rw [mem_vertexStab, lastCol, mulVec_single_iff]
  intro p
  show elMat (projection (castSuccStab 3 BinL u * rowVec v)) p (Fin.last 3) =
    (1 : Matrix (Fin 4) (Fin 4) BinL) p (Fin.last 3)
  rw [elMat_stabRow_apply, padVec_last, mul_zero, add_zero]
  exact padHom_last_right _ p

/-- **The projection `St_3(L) ⋉ L³ → J`** (Khanh, Thm 5.1). -/
def stabRowToJ : stabRow 3 BinL →* vertexStab :=
  MonoidHom.codRestrict
    ((elementaryGroup (Fin 4) BinL).subtype.comp
      ((projection (I := Fin 4) (R := BinL)).comp (stabRow 3 BinL).subtype))
    vertexStab (fun g => projection_mem_vertexStab g.1 g.2)

theorem stabRowToJ_val (g : stabRow 3 BinL) :
    (((stabRowToJ g : vertexStab) : GLFour) : Matrix (Fin 4) (Fin 4) BinL) =
      elMat (projection (g : SteinbergGroup (Fin 4) BinL)) :=
  rfl

/-- The last column of an element of `J`, in `Fin.last` form. -/
theorem vertexStab_col (k : GLFour) (hk : k ∈ vertexStab) (p : Fin 4) :
    (k : Matrix (Fin 4) (Fin 4) BinL) p (Fin.last 3) =
      (1 : Matrix (Fin 4) (Fin 4) BinL) p (Fin.last 3) :=
  (mulVec_single_iff (k : Matrix (Fin 4) (Fin 4) BinL) 3).mp (mem_vertexStab.mp hk) p

/-- **Every element of `J` has block form `[[A, 0], [v, 1]]` with `A ∈ GL_3(L) = St_3(L)`**, so
`stabRowToJ` is onto (Khanh, Thm 5.1). -/
theorem stabRowToJ_surjective : Function.Surjective stabRowToJ := by
  intro k
  have hcol : ∀ i : Fin 3,
      ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL) i.castSucc (Fin.last 3) = 0 := fun i =>
    (vertexStab_col (k : GLFour) k.2 i.castSucc).trans
      (Matrix.one_apply_ne (Fin.castSucc_ne_last i))
  have hcol' : ∀ i : Fin 3,
      (((k : GLFour)⁻¹ : GLFour) : Matrix (Fin 4) (Fin 4) BinL) i.castSucc (Fin.last 3) = 0 :=
    fun i => (vertexStab_col ((k : GLFour)⁻¹) (vertexStab.inv_mem k.2) i.castSucc).trans
      (Matrix.one_apply_ne (Fin.castSucc_ne_last i))
  have hlast : ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL) (Fin.last 3) (Fin.last 3) = 1 :=
    (vertexStab_col (k : GLFour) k.2 (Fin.last 3)).trans (Matrix.one_apply_eq _)
  obtain ⟨u, hu⟩ := LVEGen.steinbergToGL_surjective (ZMod 2) (n := 3) (by decide)
    (topBlockUnit (k : GLFour) hcol hcol')
  have hu' : ∀ i j : Fin 3, elMat (projection u) i j =
      ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL) i.castSucc j.castSucc := fun i j =>
    congrArg (fun U : (Matrix (Fin 3) (Fin 3) BinL)ˣ => (U : Matrix (Fin 3) (Fin 3) BinL) i j) hu
  have hmem : castSuccStab 3 BinL u *
      rowVec (lastRowVec ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL)) ∈ stabRow 3 BinL :=
    mem_stabRow.mpr ⟨u, lastRowVec ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL), rfl⟩
  refine ⟨⟨castSuccStab 3 BinL u *
      rowVec (lastRowVec ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL)), hmem⟩, ?_⟩
  exact Subtype.ext (Units.ext
    (stabRow_decomp ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL) hcol hlast u hu'))

/-- **The kernel of `stabRowToJ` is killed by `Ψ`** once `Ψ` kills
`castSuccStab (K₂(3, L))` (Khanh, Thm 5.1). -/
theorem stabRowToJ_ker_le {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q)
    (hΨ : ∀ k : SteinbergGroup (Fin 3) BinL, projection k = 1 →
      Ψ (castSuccStab 3 BinL k) = 1) :
    stabRowToJ.ker ≤ (Ψ.comp (stabRow 3 BinL).subtype).ker := by
  rintro ⟨g, hg⟩ hker
  obtain ⟨u, v, rfl⟩ := mem_stabRow.mp hg
  have hmat : elMat (projection (castSuccStab 3 BinL u * rowVec v)) = 1 :=
    congrArg (fun k : vertexStab => ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL))
      (MonoidHom.mem_ker.mp hker)
  obtain ⟨rfl, hu⟩ := stabRow_ker u v hmat
  rw [MonoidHom.mem_ker]
  show Ψ (castSuccStab 3 BinL u * rowVec 1) = 1
  rw [map_one, mul_one, hΨ u hu]

/-- **The relative vertex section `σ_Ψ : J →* Q`** (Khanh, Thm 5.1; tex l.733-735): the map
`J ≅ (St_3(L) ⋉ L³) / castSuccStab (K₂(3, L)) → Q` induced by `Ψ`. -/
def relSection {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q)
    (hΨ : ∀ k : SteinbergGroup (Fin 3) BinL, projection k = 1 →
      Ψ (castSuccStab 3 BinL k) = 1) :
    vertexStab →* Q :=
  stabRowToJ.liftOfRightInverse (Function.surjInv stabRowToJ_surjective)
    (Function.rightInverse_surjInv stabRowToJ_surjective)
    ⟨Ψ.comp (stabRow 3 BinL).subtype, stabRowToJ_ker_le Ψ hΨ⟩

theorem relSection_stabRowToJ {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q)
    (hΨ : ∀ k : SteinbergGroup (Fin 3) BinL, projection k = 1 →
      Ψ (castSuccStab 3 BinL k) = 1)
    (g : stabRow 3 BinL) :
    relSection Ψ hΨ (stabRowToJ g) = Ψ (g : SteinbergGroup (Fin 4) BinL) :=
  stabRowToJ.liftOfRightInverse_comp_apply (Function.surjInv stabRowToJ_surjective)
    (Function.rightInverse_surjInv stabRowToJ_surjective)
    ⟨Ψ.comp (stabRow 3 BinL).subtype, stabRowToJ_ker_le Ψ hΨ⟩ g

/-- **Relative `LiftsRoots`**: `σ_Ψ (1 + E_{ij}(a)) = Ψ (x_{ij}(a))` for `j ≠ 3`
(Khanh, Thm 5.1). -/
theorem relSection_elementaryUnit {Q : Type*} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q)
    (hΨ : ∀ k : SteinbergGroup (Fin 3) BinL, projection k = 1 →
      Ψ (castSuccStab 3 BinL k) = 1)
    (i j : Fin 4) (hij : i ≠ j) (hj : j ≠ 3) (a : BinL) :
    relSection Ψ hΨ ⟨elementaryUnit i j hij a, elementaryUnit_mem_vertexStab i j hij hj a⟩ =
      Ψ (x i j hij a) := by
  have hmem : x i j hij a ∈ stabRow 3 BinL := x_mem_stabRow (m := 3) i j hij hj a
  have heq : (⟨elementaryUnit i j hij a, elementaryUnit_mem_vertexStab i j hij hj a⟩ :
      vertexStab) = stabRowToJ ⟨x i j hij a, hmem⟩ := by
    apply Subtype.ext
    show elementaryUnit i j hij a =
      ((projection (x i j hij a) : elementaryGroup (Fin 4) BinL) : GLFour)
    rw [projection_x, elementaryRoot_val]
  rw [heq]
  exact relSection_stabRowToJ Ψ hΨ ⟨x i j hij a, hmem⟩

end

end LVRelBrown
end Full
end GroupApproximation
