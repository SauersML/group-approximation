import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.Leavitt.AryEndpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction

/-!
# Coefficient functoriality of stable `K₂ = 0` (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii: the Lean route to
infinite finitely presented simple Kazhdan groups needs stable `K₂(L_{𝔽₂}(1,2)) = 0`.  Work order
S3 of lane LVStableK2 asks for the degree-two part of the Ara–Brustenga–Cortiñas
`K`-equivalence `𝔽₂ → C_2(𝔽₂)` (Ara–Brustenga–Cortiñas, *K-theory of Leavitt path algebras*,
Münster J. Math. 2 (2009), Thm 3.6 and Sec. 7).  That proof assembles the `K`-theory of the
Cohn algebra from ultramatricial pieces, so it needs the elementary transport steps proved here,
for arbitrary rings:

* `ringMap_ringMap`, `ringMap_id_apply`: coefficient maps of Steinberg groups compose;
* `projection_ringMap`: coefficient maps cover coefficient maps of elementary groups;
* `projection_eq_one_of_ringMap`: along an injective ring map, `K₂(n, -)` is detected upstairs;
* `stableK2Trivial_of_retract`: a retract of a ring with stable `K₂ = 0` has stable `K₂ = 0`;
* `stableK2Trivial_of_ringEquiv`: stable `K₂ = 0` is invariant under ring isomorphisms.

Only modules already reachable from `GroupApproximation.lean` are imported.
-/

namespace GroupApproximation.Full.LVCohnK2

open SteinbergGroup

section Functoriality

variable {I : Type*} [Fintype I] [DecidableEq I] {R S T : Type*} [Ring R] [Ring S] [Ring T]

/-- Coefficient maps of Steinberg groups compose.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem ringMap_ringMap (f : R →+* S) (g : S →+* T) (u : SteinbergGroup I R) :
    ringMap g (ringMap f u) = ringMap (g.comp f) u := by
  have hh : (ringMap (I := I) g).comp (ringMap (I := I) f) = ringMap (I := I) (g.comp f) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change ringMap g (ringMap f (x i j hij a)) = ringMap (g.comp f) (x i j hij a)
    simp only [ringMap_x, RingHom.comp_apply]
  exact DFunLike.congr_fun hh u

/-- The identity coefficient map acts as the identity.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem ringMap_id_apply (u : SteinbergGroup I R) : ringMap (RingHom.id R) u = u := by
  have hh : ringMap (I := I) (RingHom.id R) = MonoidHom.id (SteinbergGroup I R) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change ringMap (RingHom.id R) (x i j hij a) = x i j hij a
    simp only [ringMap_x, RingHom.id_apply]
  exact DFunLike.congr_fun hh u

/-- Coefficient maps of Steinberg groups cover coefficient maps of elementary groups.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem projection_ringMap (f : R →+* S) (u : SteinbergGroup I R) :
    projection (ringMap f u) = elementaryGroupMap f (projection u) := by
  have hh : (projection (I := I) (R := S)).comp (ringMap (I := I) f) =
      (elementaryGroupMap (ι := I) f).comp (projection (I := I) (R := R)) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change projection (ringMap f (x i j hij a)) = elementaryGroupMap f (projection (x i j hij a))
    simp only [ringMap_x, projection_x]
    exact Subtype.ext (elementaryMatrixUnitMap_elementaryUnit f i j hij a).symm
  exact DFunLike.congr_fun hh u

/-- Along an injective coefficient map, an element of `St_I(R)` lies in `K₂(I, R)` as soon as its
image lies in `K₂(I, S)`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem projection_eq_one_of_ringMap (f : R →+* S) (hf : Function.Injective f)
    {u : SteinbergGroup I R} (hu : projection (ringMap f u) = 1) : projection u = 1 := by
  apply elementaryGroupMap_injective (ι := I) f hf
  have h1 := projection_ringMap f u
  rw [hu] at h1
  rw [← h1, map_one]

end Functoriality

section Retract

variable {R S : Type*} [Ring R] [Ring S]

/-- **Retracts.**  If `f : R → S` has a ring-map section `g` (`f ∘ g = id`), then stable
`K₂(R) = 0` gives stable `K₂(S) = 0`: `k ∈ K₂(n, S)` is the image of `g_* k ∈ K₂(n, R)`, which
dies after padding.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_of_retract (f : R →+* S) (g : S →+* R) (hfg : f.comp g = RingHom.id S)
    (hR : LVH2GL3.StableK2Trivial R) : LVH2GL3.StableK2Trivial S := by
  intro n k hk
  have hy : projection (ringMap (I := Fin n) g k) = 1 := by
    rw [projection_ringMap, hk, map_one]
  obtain ⟨N, hN, hyN⟩ := hR n (ringMap (I := Fin n) g k) hy
  refine ⟨N, hN, ?_⟩
  have hk' : ringMap (I := Fin n) f (ringMap (I := Fin n) g k) = k := by
    rw [ringMap_ringMap, hfg, ringMap_id_apply]
  rw [← hk', LVStableK2.indexMap_ringMap, hyN, map_one]

/-- Stable `K₂ = 0` is invariant under ring isomorphisms.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_of_ringEquiv (e : R ≃+* S) (hR : LVH2GL3.StableK2Trivial R) :
    LVH2GL3.StableK2Trivial S :=
  stableK2Trivial_of_retract e.toRingHom e.symm.toRingHom
    (RingEquiv.toRingHom_comp_symm_toRingHom e) hR

end Retract

end GroupApproximation.Full.LVCohnK2
