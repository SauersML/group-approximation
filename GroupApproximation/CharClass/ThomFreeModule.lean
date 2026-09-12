import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# The Thom class as the unique lift of `ξ^r + γ₁ ξ^{r−1} + ⋯ + γ_r`

Item 5 of §1.4 of `notes/LIX_FULL_PROGRAM_2026-09-05.md` builds the Thom class of a
rank-`r` bundle `E → X` from the pair `(P(E ⊕ 1), P(E ⊕ 1) ∖ Z)`.  Once
Leray–Hirsch is available, all that is left is *linear algebra over `H^*(X; F₂)`*,
and this file is exactly that linear algebra, with no topology in sight.

## The picture being formalized

Leray–Hirsch makes `M := H^*(P(E ⊕ 1))` a free `R := H^*(X)`-module on
`1, ξ, …, ξ^r` and `M' := H^*(P(E)) ≅ H^*(P(E ⊕ 1) ∖ Z)` a free `R`-module on
`1, ξ, …, ξ^{r−1}`, and the restriction `ρ : M → M'` is `R`-linear, sends the first
`r` basis vectors to the corresponding basis vectors of `M'`, and sends the last one
`ξ^r` to `−(γ_r · 1 + γ_{r−1} ξ + ⋯ + γ_1 ξ^{r−1})` — which *is* the defining relation
of the mod-2 Chern classes (over `F₂` the sign is invisible, and the statement below
keeps the sign so that it is true over any commutative ring).

So, with `c i := γ_{r−i}` indexed by the basis of `M'`:

* `ρ` is **surjective** (`surjective_of_basis`), which by the long exact sequence of
  the pair forces the connecting map to vanish, so that
  `j^* : H^*(pair) → M` is **injective with image `ker ρ`**;
* `ker ρ` is **free of rank one** on
  `thomGenerator b c = ξ^r + γ₁ ξ^{r−1} + ⋯ + γ_r`
  (`ker_eq_span_thomGenerator`, `existsUnique_smul_thomGenerator`);
* consequently the **Thom class** is the unique `u` with `j^*(u) = thomGenerator`
  (`existsUnique_lift`), and `H^*(pair)` is itself free of rank one on `u`
  (`existsUnique_smul_of_injective_of_range`), which is the isomorphism
  `H^{k+2r}(P(E⊕1), P(E⊕1) ∖ Z) ≅ H^k(X)` of the program note.

## Interface note for `cc-projective`

The only thing consumed here is a `Module.Basis (Fin (r+1)) R M`, a
`Module.Basis (Fin r) R M'`, and the two equations `hcast`/`hlast` describing `ρ` on
the basis.  Any packaging of Leray–Hirsch that produces those will do.
-/

namespace GroupApproximation.CharClass

variable {R : Type*} [CommRing R] {M M' : Type*}
variable [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable {r : ℕ}

/-- The class `ξ^r + γ₁ ξ^{r−1} + ⋯ + γ_r`, written in a Leray–Hirsch basis
`b = (1, ξ, …, ξ^r)` with `c i = γ_{r−i}`. -/
noncomputable def thomGenerator (b : Module.Basis (Fin (r + 1)) R M) (c : Fin r → R) : M :=
  b (Fin.last r) + ∑ i, c i • b (Fin.castSucc i)

section Coordinates

variable (b : Module.Basis (Fin (r + 1)) R M)

theorem repr_eq_coord (y : M) (j : Fin (r + 1)) : b.repr y j = b.coord j y :=
  (Module.Basis.coord_apply b j y).symm

theorem coord_last_basis_last : b.coord (Fin.last r) (b (Fin.last r)) = 1 := by
  simp [Module.Basis.coord_apply]

theorem coord_last_basis_castSucc (i : Fin r) :
    b.coord (Fin.last r) (b (Fin.castSucc i)) = 0 := by
  simp [Module.Basis.coord_apply, (Fin.castSucc_lt_last i).ne]

/-- The top coordinate of the Thom generator is `1`: it is a *monic* lift of the
Chern relation. -/
theorem coord_last_thomGenerator (c : Fin r → R) :
    b.coord (Fin.last r) (thomGenerator b c) = 1 := by
  have hsum : ∑ i : Fin r, b.coord (Fin.last r) (c i • b (Fin.castSucc i))
      = ∑ _i : Fin r, (0 : R) :=
    Finset.sum_congr rfl fun i _ => by
      rw [map_smul, coord_last_basis_castSucc b i, smul_zero]
  rw [thomGenerator, map_add, map_sum, coord_last_basis_last b, hsum,
    Finset.sum_const_zero, add_zero]

theorem coord_last_smul_thomGenerator (c : Fin r → R) (a : R) :
    b.coord (Fin.last r) (a • thomGenerator b c) = a := by
  rw [map_smul, coord_last_thomGenerator, smul_eq_mul, mul_one]

/-- An element with vanishing top coordinate is a combination of the first `r` basis
vectors. -/
theorem eq_sum_castSucc_of_coord_last_eq_zero {y : M}
    (h0 : b.coord (Fin.last r) y = 0) :
    y = ∑ i : Fin r, b.coord (Fin.castSucc i) y • b (Fin.castSucc i) := by
  have h1 : ∑ j : Fin (r + 1), b.repr y j • b j = y := b.sum_repr y
  rw [Fin.sum_univ_castSucc, repr_eq_coord b y (Fin.last r), h0, zero_smul, add_zero] at h1
  have h2 : ∑ i : Fin r, b.coord (Fin.castSucc i) y • b (Fin.castSucc i)
      = ∑ i : Fin r, b.repr y (Fin.castSucc i) • b (Fin.castSucc i) :=
    Finset.sum_congr rfl fun i _ => by rw [repr_eq_coord b y (Fin.castSucc i)]
  exact (h2.trans h1).symm

end Coordinates

section Restriction

variable (b : Module.Basis (Fin (r + 1)) R M) (b' : Module.Basis (Fin r) R M')
variable (c : Fin r → R) {ρ : M →ₗ[R] M'}

/-- **The restriction is surjective.**  Topologically: `H^*(P(E ⊕ 1)) → H^*(P(E))` is
onto, because Leray–Hirsch bases correspond for the first `r` powers of `ξ`.  This is
what makes the connecting map of the pair vanish. -/
theorem surjective_of_basis (hcast : ∀ i : Fin r, ρ (b (Fin.castSucc i)) = b' i) :
    Function.Surjective ρ := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← b'.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact SetLike.mem_coe.2 (LinearMap.mem_range.2 ⟨b (Fin.castSucc i), hcast i⟩)

/-- **The Thom generator lies in the kernel.**  This is the Chern relation
`ξ^r + γ₁ ξ^{r−1} + ⋯ + γ_r = 0` in `H^*(P(E))`. -/
theorem map_thomGenerator (hcast : ∀ i : Fin r, ρ (b (Fin.castSucc i)) = b' i)
    (hlast : ρ (b (Fin.last r)) = -∑ i, c i • b' i) :
    ρ (thomGenerator b c) = 0 := by
  have hsum : ∑ i : Fin r, ρ (c i • b (Fin.castSucc i)) = ∑ i : Fin r, c i • b' i :=
    Finset.sum_congr rfl fun i _ => by rw [map_smul, hcast i]
  rw [thomGenerator, map_add, map_sum, hsum, hlast, neg_add_cancel]

/-- An element of the kernel whose top coordinate vanishes is zero: the first `r` basis
vectors of `M` map to a basis of `M'`. -/
theorem eq_zero_of_coord_last_eq_zero (hcast : ∀ i : Fin r, ρ (b (Fin.castSucc i)) = b' i)
    {y : M} (h0 : b.coord (Fin.last r) y = 0) (hy : ρ y = 0) : y = 0 := by
  have hexp := eq_sum_castSucc_of_coord_last_eq_zero b h0
  have hsum : ∑ i : Fin r, b.coord (Fin.castSucc i) y • b' i = 0 := by
    have hy' : ρ (∑ i : Fin r, b.coord (Fin.castSucc i) y • b (Fin.castSucc i)) = 0 := by
      rw [← hexp]; exact hy
    have hmap : ∑ i : Fin r, ρ (b.coord (Fin.castSucc i) y • b (Fin.castSucc i))
        = ∑ i : Fin r, b.coord (Fin.castSucc i) y • b' i :=
      Finset.sum_congr rfl fun i _ => by rw [map_smul, hcast i]
    rw [map_sum, hmap] at hy'
    exact hy'
  have hind : ∀ i : Fin r, b.coord (Fin.castSucc i) y = 0 := fun i =>
    linearIndependent_iff'.1 b'.linearIndependent Finset.univ _ hsum i (Finset.mem_univ i)
  rw [hexp]
  exact Finset.sum_eq_zero fun i _ => by rw [hind i, zero_smul]

/-- **The kernel is free of rank one on the Thom generator**, in the explicit form: the
coefficient is the top coordinate. -/
theorem eq_coord_last_smul_thomGenerator (hcast : ∀ i : Fin r, ρ (b (Fin.castSucc i)) = b' i)
    (hlast : ρ (b (Fin.last r)) = -∑ i, c i • b' i) {x : M} (hx : ρ x = 0) :
    x = b.coord (Fin.last r) x • thomGenerator b c := by
  have hzero : x - b.coord (Fin.last r) x • thomGenerator b c = 0 := by
    refine eq_zero_of_coord_last_eq_zero b b' hcast ?_ ?_
    · rw [map_sub, coord_last_smul_thomGenerator, sub_self]
    · rw [map_sub, hx, map_smul, map_thomGenerator b b' c hcast hlast, smul_zero, sub_zero]
  exact sub_eq_zero.1 hzero

/-- **Uniqueness of the coefficient.**  Every element of `ker ρ` is `a • (ξ^r + γ₁ ξ^{r−1}
+ ⋯ + γ_r)` for exactly one `a ∈ H^*(X)`; this is the Leray–Hirsch isomorphism
`ker ρ ≅ H^{*−2r}(X)`. -/
theorem existsUnique_smul_thomGenerator (hcast : ∀ i : Fin r, ρ (b (Fin.castSucc i)) = b' i)
    (hlast : ρ (b (Fin.last r)) = -∑ i, c i • b' i) {x : M} (hx : ρ x = 0) :
    ∃! a : R, x = a • thomGenerator b c := by
  refine ⟨b.coord (Fin.last r) x, eq_coord_last_smul_thomGenerator b b' c hcast hlast hx, ?_⟩
  intro a ha
  rw [ha, coord_last_smul_thomGenerator]

/-- The kernel of the restriction is the `R`-span of the Thom generator. -/
theorem ker_eq_span_thomGenerator (hcast : ∀ i : Fin r, ρ (b (Fin.castSucc i)) = b' i)
    (hlast : ρ (b (Fin.last r)) = -∑ i, c i • b' i) :
    LinearMap.ker ρ = Submodule.span R {thomGenerator b c} := by
  apply le_antisymm
  · rw [SetLike.le_def]
    intro x hx
    exact Submodule.mem_span_singleton.2
      ⟨b.coord (Fin.last r) x,
        (eq_coord_last_smul_thomGenerator b b' c hcast hlast (LinearMap.mem_ker.1 hx)).symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact SetLike.mem_coe.2 (LinearMap.mem_ker.2 (map_thomGenerator b b' c hcast hlast))

end Restriction

section Lift

variable {P : Type*} [AddCommGroup P] [Module R P]

/-- **The Thom class exists and is unique.**  If `jm` (the map `j^*` of the pair) is
injective with image `ker ρ`, there is exactly one class `u` restricting to
`ξ^r + γ₁ ξ^{r−1} + ⋯ + γ_r`.

Injectivity of `jm` is the long exact sequence of the pair together with
`surjective_of_basis` in the previous degree; the image condition is exactness at
`H^*(P(E ⊕ 1))`. -/
theorem existsUnique_lift {ρ : M →ₗ[R] M'} {w : M} (jm : P →ₗ[R] M)
    (hinj : Function.Injective jm)
    (hrange : LinearMap.range jm = LinearMap.ker ρ) (hw : ρ w = 0) :
    ∃! u : P, jm u = w := by
  have hmem : w ∈ LinearMap.range jm := by
    rw [hrange]; exact LinearMap.mem_ker.2 hw
  obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hmem
  exact ⟨u, hu, fun v hv => hinj (hv.trans hu.symm)⟩

/-- **`H^*(pair)` is free of rank one on the Thom class.**  Transporting
`existsUnique_smul_thomGenerator` along the injection `jm` with image `ker ρ`: every
element of `P` is a unique multiple of the class `u` lifting the Thom generator.  This
is the isomorphism `H^{k+2r}(P(E⊕1), P(E⊕1) ∖ Z) ≅ H^k(X)`. -/
theorem existsUnique_smul_of_injective_of_range
    (b : Module.Basis (Fin (r + 1)) R M) (b' : Module.Basis (Fin r) R M') (c : Fin r → R)
    {ρ : M →ₗ[R] M'} (hcast : ∀ i : Fin r, ρ (b (Fin.castSucc i)) = b' i)
    (hlast : ρ (b (Fin.last r)) = -∑ i, c i • b' i)
    (jm : P →ₗ[R] M) (hinj : Function.Injective jm)
    (hrange : LinearMap.range jm = LinearMap.ker ρ)
    {u : P} (hu : jm u = thomGenerator b c) (x : P) :
    ∃! a : R, x = a • u := by
  have hxker : ρ (jm x) = 0 := by
    have : jm x ∈ LinearMap.ker ρ := by
      rw [← hrange]; exact LinearMap.mem_range.2 ⟨x, rfl⟩
    exact LinearMap.mem_ker.1 this
  obtain ⟨a, ha, hauniq⟩ := existsUnique_smul_thomGenerator b b' c hcast hlast hxker
  refine ⟨a, hinj ?_, ?_⟩
  · rw [map_smul, hu, ← ha]
  · intro a' ha'
    exact hauniq a' (by rw [ha', map_smul, hu])

end Lift

end GroupApproximation.CharClass
