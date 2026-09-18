import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Restricting invariant function spaces along equivariant embeddings (bh-met-87c, part 5)

`eHighWitt_transport` takes an injective additive map `ι : M →+ N` that intertwines
`actM q` and `actN q`, together with a space `V ⊆ (N → L)` of functions.  If `V` is
finite-dimensional, translation-stable, `actN`-stable and separating, then its restriction
`W = {f ∘ ι | f ∈ V}` has the same four properties on `M`.

* Finiteness: `W` is the image of `V` under the linear map `LinearMap.funLeft L L ι`.
* Stability: `(f ∘ ι)(x + m) = (f ∘ (· + ι m))(ι x)` and `(f ∘ ι)(actM q x) = (f ∘ actN q)(ι x)`.
* Separation: for `m ≠ 0` we have `ι m ≠ 0 = ι 0`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- Restriction of an invariant separating finite-dimensional function space along an
injective equivariant additive embedding. -/
theorem eHighWitt_transport {L M N Q : Type} [Field L] [AddCommGroup M] [AddCommGroup N]
    (ι : M →+ N) (hι : Function.Injective ι) (actM : Q → M → M) (actN : Q → N → N)
    (hcompat : ∀ (q : Q) (m : M), ι (actM q m) = actN q (ι m))
    (V : Submodule L (N → L)) (hfd : FiniteDimensional L V)
    (htrans : ∀ n : N, ∀ f ∈ V, (fun x => f (x + n)) ∈ V)
    (hact : ∀ q : Q, ∀ f ∈ V, (fun x => f (actN q x)) ∈ V)
    (hsep : ∀ n : N, n ≠ 0 → ∃ f ∈ V, f n ≠ f 0) :
    ∃ W : Submodule L (M → L), FiniteDimensional L W ∧
      (∀ m : M, ∀ f ∈ W, (fun x => f (x + m)) ∈ W) ∧
      (∀ q : Q, ∀ f ∈ W, (fun x => f (actM q x)) ∈ W) ∧
      (∀ m : M, m ≠ 0 → ∃ f ∈ W, f m ≠ f 0) := by
  refine ⟨V.map (LinearMap.funLeft L L ι), ?_, ?_, ?_, ?_⟩
  · have hfg : V.FG := Module.Finite.iff_fg.mp hfd
    exact Module.Finite.iff_fg.mpr (hfg.map _)
  · intro m f hf
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
    refine Submodule.mem_map.mpr ⟨fun y => g (y + ι m), htrans (ι m) g hg, ?_⟩
    funext x
    simp only [LinearMap.funLeft_apply, map_add]
  · intro q f hf
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
    refine Submodule.mem_map.mpr ⟨fun y => g (actN q y), hact q g hg, ?_⟩
    funext x
    simp only [LinearMap.funLeft_apply, hcompat]
  · intro m hm
    have hιm : ι m ≠ 0 := fun h => hm (hι (h.trans (map_zero ι).symm))
    obtain ⟨g, hg, hne⟩ := hsep (ι m) hιm
    refine ⟨LinearMap.funLeft L L ι g, Submodule.mem_map_of_mem hg, ?_⟩
    simp only [LinearMap.funLeft_apply, map_zero]
    exact hne

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_transport

end GroupApproximation.BooneHigman.Metabelian.Coprimary
