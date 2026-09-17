import Mathlib.Data.Fin.Embedding
import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.Steinberg.ElementaryIndexPadding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSuperperfect.Superperfect

/-!
# `H₂(GL₃(L); ℤ) = 0` from stable `K₂(L) = 0` and rank-by-rank injective stability (lane LVH2GL3)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`) cites Caprace–Rémy: infinite
finitely presented simple Kazhdan groups exist.  The Lean route needs `K₂(4, L) = ⊥` for
`L = L_{𝔽₂}(1,2)` (Khanh, arXiv:2609.08428, Thm 5.1).  One leaf of that proof (leaf T1b.iii) is
`H₂(GL₃(L); ℤ) = 0` (Khanh, Thm 4.4).  Since `GL_r(L) ≅ Lˣ` for every `r ≥ 1`, this is the
binder `hsp`: `Lˣ` is superperfect (`LVSuperperfect.IsSuperperfect`).

The classical proof has two parts of different nature:

* **stable `K₂(L) = 0`** (`StableK2Trivial`): every element of `K₂(n, L)` dies in some `St_N(L)`.
  Source: Ara–Brustenga–Cortiñas (2009), `K_*(L_k(1,2)) = 0`;
* **injective stability** (`K2StabInjective`): `K₂(m, L) → K₂(m + 1, L)` is injective for `m ≥ 5`.
  Source: homological stability for `GL_m(L)` (Khanh, Thm 2.2; Quillen's weight argument on the
  frame complex).

This file proves the formal part of the reduction, for any ring `R`:

* `indexMap_castLEEmb_self`, `indexMap_castLEEmb_castLEEmb`: identity padding is functorial;
* `projection_indexMap`: padding of Steinberg groups covers padding of elementary groups, so it
  maps `K₂(n, R)` into `K₂(N, R)`;
* `eq_one_of_indexMap_eq_one`: rank-by-rank injective stability from rank `n` telescopes;
* `projection_ker_eq_bot_of_stable`: stable triviality plus injective stability from rank `n`
  give `K₂(n, R) = ⊥`;
* `binaryLeavittUnits_isSuperperfect_of_stable`: for `L`, from rank `5` this gives `hsp`
  (through `LVSuperperfect.binaryLeavittUnits_isSuperperfect_of_K2_eq_bot`, i.e.
  Kervaire–Steinberg and `St₅(L) ≅ E₅(L) ≅ Lˣ`).

Every imported module is already reachable from `GroupApproximation.lean`.  In particular the
foreign orphan `LeavittK2/StableReduction/StableKTwo` is not imported.  Its finite-stage statements
use `BooneHigman.SteinbergBasic.K2 (Fin n) R`, which is by definition
`(SteinbergGroup.projection).ker`, the kernel used here.
-/

namespace GroupApproximation.Full.LVH2GL3

open SteinbergGroup

variable {R : Type*} [Ring R]

/-! ### Identity padding of Steinberg groups -/

/-- Padding along the identity `Fin n ↪ Fin n` is the identity.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem indexMap_castLEEmb_self {n : ℕ} (h : n ≤ n) (g : SteinbergGroup (Fin n) R) :
    indexMap (Fin.castLEEmb h) g = g := by
  have hh : indexMap (R := R) (Fin.castLEEmb h) = MonoidHom.id (SteinbergGroup (Fin n) R) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change indexMap (Fin.castLEEmb h) (x i j hij a) = x i j hij a
    simp only [indexMap_x, Fin.castLEEmb_apply, Fin.castLE_refl]
  exact DFunLike.congr_fun hh g

/-- Padding `Fin n ↪ Fin m ↪ Fin p` in two steps is padding in one step. -/
theorem indexMap_castLEEmb_castLEEmb {n m p : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ p)
    (g : SteinbergGroup (Fin n) R) :
    indexMap (Fin.castLEEmb h₂) (indexMap (Fin.castLEEmb h₁) g) =
      indexMap (Fin.castLEEmb (h₁.trans h₂)) g := by
  have hh : (indexMap (R := R) (Fin.castLEEmb h₂)).comp (indexMap (Fin.castLEEmb h₁)) =
      indexMap (Fin.castLEEmb (h₁.trans h₂)) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change indexMap (Fin.castLEEmb h₂) (indexMap (Fin.castLEEmb h₁) (x i j hij a)) =
      indexMap (Fin.castLEEmb (h₁.trans h₂)) (x i j hij a)
    simp only [indexMap_x, Fin.castLEEmb_apply, Fin.castLE_castLE]
  exact DFunLike.congr_fun hh g

/-- Index padding of Steinberg groups covers index padding of elementary groups. -/
theorem projection_indexMap {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ↪ J) (g : SteinbergGroup I R) :
    projection (indexMap e g) = ElementaryPadding.elementaryPad e (projection g) := by
  have hh : (projection (I := J) (R := R)).comp (indexMap e) =
      (ElementaryPadding.elementaryPad e).comp (projection (I := I) (R := R)) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change projection (indexMap e (x i j hij a)) =
      ElementaryPadding.elementaryPad e (projection (x i j hij a))
    rw [indexMap_x, projection_x, projection_x, ElementaryPadding.elementaryPad_elementaryRoot]
  exact DFunLike.congr_fun hh g

/-- Padding maps `K₂(n, R)` into `K₂(N, R)`. -/
theorem projection_indexMap_eq_one {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ↪ J) {g : SteinbergGroup I R} (hg : projection g = 1) :
    projection (indexMap e g) = 1 := by
  rw [projection_indexMap, hg, map_one]

/-! ### The two stable ingredients -/

/-- **Stable `K₂(R) = 0`**, in finite-stage form: every `k ∈ K₂(n, R)` becomes trivial in some
`St_N(R)`, `n ≤ N`, under identity padding.  For `R = L_{𝔽₂}(1,2)` this is
Ara–Brustenga–Cortiñas (2009), `K₂(L) = 0`. (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
def StableK2Trivial (R : Type*) [Ring R] : Prop :=
  ∀ (n : ℕ) (k : SteinbergGroup (Fin n) R), projection k = 1 →
    ∃ (N : ℕ) (h : n ≤ N), indexMap (Fin.castLEEmb h) k = 1

/-- **Injective stability for `K₂` at rank `m`**: `K₂(m, R) → K₂(m + 1, R)` is injective.
For `R = L_{𝔽₂}(1,2)` and `m ≥ 5` this is homological stability (Khanh, arXiv:2609.08428,
Thm 2.2). (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
def K2StabInjective (R : Type*) [Ring R] (m : ℕ) : Prop :=
  ∀ k : SteinbergGroup (Fin m) R, projection k = 1 →
    indexMap (Fin.castLEEmb (Nat.le_succ m)) k = 1 → k = 1

/-- If `K₂(m, R) = ⊥`, injective stability at rank `m` holds trivially. -/
theorem k2StabInjective_of_ker_eq_bot {m : ℕ}
    (hK : (projection (I := Fin m) (R := R)).ker = ⊥) : K2StabInjective R m := by
  intro k hk _
  exact (Subgroup.eq_bot_iff_forall _).mp hK k (MonoidHom.mem_ker.mpr hk)

/-- **Telescoping.**  If `K₂(m, R) → K₂(m + 1, R)` is injective for every `m ≥ n`, then an element
of `K₂(n, R)` that dies in some `St_N(R)` is trivial. -/
theorem eq_one_of_indexMap_eq_one {n : ℕ} (hT : ∀ m, n ≤ m → K2StabInjective R m)
    {k : SteinbergGroup (Fin n) R} (hk : projection k = 1) (N : ℕ) (h : n ≤ N)
    (hN : indexMap (Fin.castLEEmb h) k = 1) : k = 1 := by
  revert hN
  induction N, h using Nat.le_induction with
  | base =>
    intro hN
    exact (indexMap_castLEEmb_self (Nat.le_refl n) k).symm.trans hN
  | succ N hnN ih =>
    intro hN
    apply ih
    apply hT N hnN (indexMap (Fin.castLEEmb hnN) k) (projection_indexMap_eq_one _ hk)
    exact (indexMap_castLEEmb_castLEEmb hnN (Nat.le_succ N) k).trans hN

/-- **`K₂(n, R) = ⊥`** from stable triviality and injective stability from rank `n`. -/
theorem projection_ker_eq_bot_of_stable {n : ℕ} (hS : StableK2Trivial R)
    (hT : ∀ m, n ≤ m → K2StabInjective R m) :
    (projection (I := Fin n) (R := R)).ker = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr ?_
  intro k hk
  have hk' : projection k = 1 := MonoidHom.mem_ker.mp hk
  obtain ⟨N, h, hN⟩ := hS n k hk'
  exact eq_one_of_indexMap_eq_one hT hk' N h hN

/-- **Leaf T1b.iii (`H₂(GL₃(L); ℤ) = 0`, binder `hsp`) from the two stable ingredients.**
For `L = L_{𝔽₂}(1,2)`: stable `K₂(L) = 0` (Ara–Brustenga–Cortiñas) and injective `K₂`-stability
from rank `5` (Khanh, arXiv:2609.08428, Thm 2.2) give `K₂(5, L) = ⊥`, hence `Lˣ` is superperfect.
Via `LVSuperperfect.gl_isSuperperfect_of_binaryLeavittUnits` this is `H₂(GL₃(L); ℤ) = 0`
(Khanh, Thm 4.4). (`simple_kazhdan_sofic_group.tex` l.733-735, `sec:questions`.) -/
theorem binaryLeavittUnits_isSuperperfect_of_stable
    (hS : StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))
    (hT : ∀ m, 5 ≤ m → K2StabInjective (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) m) :
    LVSuperperfect.IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) :=
  LVSuperperfect.binaryLeavittUnits_isSuperperfect_of_K2_eq_bot (n := 5) (Nat.le_refl 5)
    (projection_ker_eq_bot_of_stable hS hT)

end GroupApproximation.Full.LVH2GL3
