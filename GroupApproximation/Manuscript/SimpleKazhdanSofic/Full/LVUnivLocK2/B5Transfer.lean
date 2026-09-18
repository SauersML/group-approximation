import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Coefficients

/-!
# From an exact localization sequence to finite-stage base surjectivity (lane LVUnivLocK2, B5)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`, "The finitely presented case"),
leaf T1b.iii, input W1 (stable `K₂(L_{𝔽₂}(1,2)) = 0`).  Core-B of lane LVK2Route
(`LVK2Route.binaryLeavitt_stableK2Trivial_of_freeBaseSurjective`) reduces W1 to
`LVStableK2.StableK2BaseSurjective LVK2Route.freeToLeavitt`.  The classical input is the
localization sequence of a stably flat universal localization (Neeman–Ranicki 2004;
Bergman–Dicks 1978 for stable flatness of `𝔽₂⟨x₀,x₁⟩ → L_{𝔽₂}(1,2)`):
`K₂(R) → K₂(Σ⁻¹R) → K₁(T)`, exact in the middle, with `K₁(T) = 0`.

That sequence lives in *some* model of `K₂` (Quillen's `Q`-construction, Waldhausen's `S•`),
while `StableK2BaseSurjective` is a statement about finite-stage Steinberg groups.  This file
(sub-step B5) proves the translation, for arbitrary rings and arbitrary models:

* `StableK2Model R A`: a group `A` presented by classes of finite-stage elements of `K₂(n, R)`,
  compatible with padding, exhausting `A`, and detecting stable equality.  Any group isomorphic
  to `colim_n K₂(n, R)` is one (`StableK2Model.transport`; the canonical model is in `B5Canonical`);
* `StableK2Model.Natural`: compatibility of a homomorphism `α : A → B` with `ringMap f`;
* `stableK2BaseSurjective_of_surjective`, `surjective_of_stableK2BaseSurjective`,
  `stableK2BaseSurjective_iff_surjective`: for natural `α`, finite-stage base surjectivity is
  exactly surjectivity of `α`;
* `stableK2BaseSurjective_of_exact`: exactness of `A → B → C` at `B` with `C` trivial gives
  base surjectivity.  This is the form in which the localization sequence is used, with
  `C = K₁(T)` for the torsion category `T`.

All statements are proved; there are no hypotheses standing for literature theorems (the
hypotheses are ordinary algebraic data: groups, homomorphisms, exactness).
-/

namespace GroupApproximation.Full.LVUnivLocK2

open SteinbergGroup

/-- A coefficient map sends `K₂(n, R)` into `K₂(n, S)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem projection_ringMap_eq_one {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {n : ℕ}
    {y : SteinbergGroup (Fin n) R} (hy : projection y = 1) : projection (ringMap f y) = 1 := by
  rw [LVCohnK2.projection_ringMap, hy, map_one]

/-- A **model of stable `K₂(R)`** in a group `A`.  Every element `k ∈ K₂(n, R)` has a class
`cls n k hk ∈ A`; classes are invariant under padding; every element of `A` is a class; and two
elements with the same class agree after padding to a common rank.  Equivalently, `cls` induces
a bijection `colim_n K₂(n, R) → A` (see `B5Canonical` for the colimit itself).  Quillen's
`K₂(R) = π₃ BQ(P(R))` with the Steinberg comparison (`K₂ = H₂(E(R))`, Quillen's `+ = Q`) is such a
model.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
structure StableK2Model (R : Type*) [Ring R] (A : Type*) [Group A] where
  /-- The class of a finite-stage element of `K₂(n, R)`. -/
  cls : ∀ (n : ℕ) (k : SteinbergGroup (Fin n) R), projection k = 1 → A
  /-- Classes are invariant under padding. -/
  cls_indexMap : ∀ (n N : ℕ) (h : n ≤ N) (k : SteinbergGroup (Fin n) R) (hk : projection k = 1),
    cls N (indexMap (Fin.castLEEmb h) k) (LVH2GL3.projection_indexMap_eq_one _ hk) = cls n k hk
  /-- Every element of the model is a class. -/
  exists_cls : ∀ a : A, ∃ (n : ℕ) (k : SteinbergGroup (Fin n) R) (hk : projection k = 1),
    cls n k hk = a
  /-- Elements with equal classes agree after padding to a common rank. -/
  exists_indexMap_eq : ∀ (n m : ℕ) (k : SteinbergGroup (Fin n) R)
    (l : SteinbergGroup (Fin m) R) (hk : projection k = 1) (hl : projection l = 1),
    cls n k hk = cls m l hl →
      ∃ (N : ℕ) (hn : n ≤ N) (hm : m ≤ N),
        indexMap (Fin.castLEEmb hn) k = indexMap (Fin.castLEEmb hm) l

section Model

variable {R S : Type*} [Ring R] [Ring S]

namespace StableK2Model

variable {A B A' : Type*} [Group A] [Group B] [Group A']

/-- A homomorphism `α` between models of stable `K₂(R)` and `K₂(S)` is **natural** for `f` if it
sends the class of `y ∈ K₂(n, R)` to the class of `f_* y ∈ K₂(n, S)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def Natural (MR : StableK2Model R A) (MS : StableK2Model S B) (f : R →+* S) (α : A →* B) :
    Prop :=
  ∀ (n : ℕ) (y : SteinbergGroup (Fin n) R) (hy : projection y = 1),
    MS.cls n (ringMap f y) (projection_ringMap_eq_one f hy) = α (MR.cls n y hy)

/-- Transport of a model along a group isomorphism.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def transport (M : StableK2Model R A) (e : A ≃* A') : StableK2Model R A' where
  cls n k hk := e (M.cls n k hk)
  cls_indexMap n N h k hk := congrArg (⇑e) (M.cls_indexMap n N h k hk)
  exists_cls a := by
    obtain ⟨n, k, hk, hka⟩ := M.exists_cls (e.symm a)
    refine ⟨n, k, hk, ?_⟩
    change e (M.cls n k hk) = a
    rw [hka, MulEquiv.apply_symm_apply]
  exists_indexMap_eq n m k l hk hl hkl :=
    M.exists_indexMap_eq n m k l hk hl (e.injective hkl)

/-- The class map of a transported model.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem transport_cls (M : StableK2Model R A) (e : A ≃* A') (n : ℕ)
    (k : SteinbergGroup (Fin n) R) (hk : projection k = 1) :
    (M.transport e).cls n k hk = e (M.cls n k hk) :=
  rfl

/-- The class of an element does not depend on how it is written.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cls_eq_of_eq (M : StableK2Model R A) {n : ℕ} {k k' : SteinbergGroup (Fin n) R}
    (h : k = k') (hk : projection k = 1) (hk' : projection k' = 1) :
    M.cls n k hk = M.cls n k' hk' := by
  subst h
  rfl

end StableK2Model

end Model

section Transfer

variable {R S : Type*} [Ring R] [Ring S] {A B C : Type*} [Group A] [Group B] [Group C]

/-- **B5, surjective form.**  If a homomorphism `α` between models of stable `K₂(R)` and
`K₂(S)` is natural for `f` and surjective, then `f` is stably surjective on finite-stage `K₂`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2BaseSurjective_of_surjective (f : R →+* S) (MR : StableK2Model R A)
    (MS : StableK2Model S B) (α : A →* B) (hnat : MR.Natural MS f α)
    (hα : Function.Surjective α) : LVStableK2.StableK2BaseSurjective f := by
  intro n k hk
  obtain ⟨a, ha⟩ := hα (MS.cls n k hk)
  obtain ⟨N, y, hy1, hya⟩ := MR.exists_cls a
  have hcl : MS.cls N (ringMap f y) (projection_ringMap_eq_one f hy1) = MS.cls n k hk := by
    rw [hnat N y hy1, hya, ha]
  obtain ⟨M, hNM, hnM, heq⟩ :=
    MS.exists_indexMap_eq N n (ringMap f y) k (projection_ringMap_eq_one f hy1) hk hcl
  refine ⟨M, hnM, indexMap (Fin.castLEEmb hNM) y,
    LVH2GL3.projection_indexMap_eq_one _ hy1, ?_⟩
  exact (LVStableK2.indexMap_ringMap (Fin.castLEEmb hNM) f y).symm.trans heq

/-- **B5, converse.**  Finite-stage base surjectivity makes every natural `α` surjective.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem surjective_of_stableK2BaseSurjective (f : R →+* S) (MR : StableK2Model R A)
    (MS : StableK2Model S B) (α : A →* B) (hnat : MR.Natural MS f α)
    (hB : LVStableK2.StableK2BaseSurjective f) : Function.Surjective α := by
  intro b
  obtain ⟨n, k, hk, hkb⟩ := MS.exists_cls b
  obtain ⟨N, h, y, hy1, hy⟩ := hB n k hk
  refine ⟨MR.cls N y hy1, ?_⟩
  calc α (MR.cls N y hy1)
      = MS.cls N (ringMap f y) (projection_ringMap_eq_one f hy1) := (hnat N y hy1).symm
    _ = MS.cls N (indexMap (Fin.castLEEmb h) k) (LVH2GL3.projection_indexMap_eq_one _ hk) :=
        MS.cls_eq_of_eq hy _ _
    _ = MS.cls n k hk := MS.cls_indexMap n N h k hk
    _ = b := hkb

/-- **B5, exact reformulation.**  For a natural `α`, finite-stage base surjectivity of `f` is
surjectivity of `α`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2BaseSurjective_iff_surjective (f : R →+* S) (MR : StableK2Model R A)
    (MS : StableK2Model S B) (α : A →* B) (hnat : MR.Natural MS f α) :
    LVStableK2.StableK2BaseSurjective f ↔ Function.Surjective α :=
  ⟨surjective_of_stableK2BaseSurjective f MR MS α hnat,
    stableK2BaseSurjective_of_surjective f MR MS α hnat⟩

/-- **B5, localization form.**  If `A → B → C` is exact at `B` (every `b` with `δ b = 1` comes
from `A`), `C` is trivial, and `α` is natural for `f`, then `f` is stably surjective on
finite-stage `K₂`.  Applied with the Neeman–Ranicki sequence `K₂(R) → K₂(Σ⁻¹R) → K₁(T)` and
`K₁(T) = 0`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2BaseSurjective_of_exact (f : R →+* S) (MR : StableK2Model R A)
    (MS : StableK2Model S B) (α : A →* B) (δ : B →* C) (hnat : MR.Natural MS f α)
    (hexact : ∀ b : B, δ b = 1 → ∃ a : A, α a = b) (hC : ∀ c : C, c = 1) :
    LVStableK2.StableK2BaseSurjective f :=
  stableK2BaseSurjective_of_surjective f MR MS α hnat fun b => hexact b (hC (δ b))

end Transfer

end GroupApproximation.Full.LVUnivLocK2
