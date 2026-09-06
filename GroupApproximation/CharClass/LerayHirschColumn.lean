import GroupApproximation.CharClass.ProjectiveSpaceCohomology

/-!
# The shifted-sum column of the Leray–Hirsch ladder

Leray–Hirsch is proved by induction over a finite trivialising cover, comparing
two Mayer–Vietoris sequences through the five lemma.  The right-hand column is the
sequence of the total space.  The left-hand column, built here, is the direct sum
over `i < r` of the sequence of the base **shifted by `2i`**, because the
Leray–Hirsch map sends a family `(a_i)` to `∑ π^*(a_i) ⌣ ξ^i`.

## The one design decision

Which summands appear in degree `n` depends on `n`: only those with `2i ≤ n`.
Indexing by `Fin r` and writing the `i`-th entry in `H^{n-2i}` is *wrong* on the
nose, because truncated subtraction turns the absent summands into spurious
copies of `H^0(X)`.  Rather than let the index type vary with the degree, which
would make the connecting map change shape, the junk is cut out by a subgroup:

```text
lhDomain X r n  =  { c : ∀ i : Fin r, H^{n-2i}(X)  //  c i = 0 whenever 2i > n }.
```

Everything then acts componentwise.  The connecting map lands in the subgroup for
free, since a family vanishing wherever `2i > n` vanishes in particular wherever
`2i > n + 1`.

## The two Mayer–Vietoris facts

`MVFacts` bundles them.  `delta_cup` is the linearity of the connecting map over
classes pulled back from the ambient space, which is the ladder's connecting-map
rung.  `exactZero` is exactness at the left end, and it is *not* an independent
convenience: the column is exact at every index by the base sequence except at
the boundary index `2i = n + 1`, where the source component is forced to zero by
the subgroup condition while the target component is `H^0(X)`, and exactness
there is exactly that injectivity.  It is needed again to place the preimage in
`colExactSum`.

Both are hypotheses here and theorems in `cc-cohom-api`'s Mayer–Vietoris files;
everything above them is proved now, so instantiating `MVFacts` is two lines.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

variable {X U V W : TopCat.{0}}

/-! ## 1. The two Mayer–Vietoris facts -/

/-- **The two facts the Leray–Hirsch ladder uses beyond the sequence itself.** -/
structure MVFacts (mv : MVSequence X U V W) : Prop where
  /-- The connecting map is linear over classes pulled back from the ambient space.
  This is the ladder's connecting-map rung. -/
  delta_cup : ∀ (p q : ℕ) (a : Hmod2 W p) (b : Hmod2 X q),
      mv.δ (p + q) (cup a (mv.resWU q (mv.resU q b)))
        = cohCast (by omega) (cup (mv.δ p a) b)
  /-- Exactness at the left end, `0 → H^0(X) → H^0(U) ⊕ H^0(V)`. -/
  exactZero : ∀ x : Hmod2 X 0, mv.resU 0 x = 0 → mv.resV 0 x = 0 → x = 0

/-! ## 2. The degree-`n` term of the column -/

/-- The degree-`n` term of the shifted sum: families indexed by `Fin r` with the
`i`-th entry in `H^{n-2i}`, cut down by the vanishing that removes the summands
truncated subtraction would otherwise invent. -/
def lhDomain (X : TopCat.{0}) (r n : ℕ) :
    AddSubgroup ((i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) where
  carrier := {c | ∀ i : Fin r, n < 2 * (i : ℕ) → c i = 0}
  add_mem' {a b} ha hb := by
    intro i hi
    show a i + b i = 0
    rw [ha i hi, hb i hi, add_zero]
  zero_mem' := by
    intro i _
    rfl
  neg_mem' {a} ha := by
    intro i hi
    show -a i = 0
    rw [ha i hi, neg_zero]

@[simp] theorem lhDomain_coe_apply {r n : ℕ} (c : lhDomain X r n) (i : Fin r) :
    (c : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) i
      = (c : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) i := rfl

theorem lhDomain_vanish {r n : ℕ} (c : lhDomain X r n) (i : Fin r) (hi : n < 2 * (i : ℕ)) :
    (c : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) i = 0 :=
  c.2 i hi

theorem lhDomain_ext {r n : ℕ} {c d : lhDomain X r n}
    (h : ∀ i : Fin r, (c : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) i
      = (d : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) i) : c = d :=
  Subtype.ext (funext h)

/-! ## 3. The five maps, componentwise -/

/-- Restriction to `U`, on the column. -/
def colResU (mv : MVSequence X U V W) (r n : ℕ) : lhDomain X r n →+ lhDomain U r n where
  toFun c := ⟨fun i => mv.resU _ ((c : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) i), by
    intro i hi
    dsimp only
    rw [lhDomain_vanish c i hi, map_zero]⟩
  map_zero' := lhDomain_ext fun i => by dsimp only; exact map_zero _
  map_add' a b := lhDomain_ext fun i => by dsimp only; exact map_add _ _ _

/-- Restriction to `V`, on the column. -/
def colResV (mv : MVSequence X U V W) (r n : ℕ) : lhDomain X r n →+ lhDomain V r n where
  toFun c := ⟨fun i => mv.resV _ ((c : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) i), by
    intro i hi
    dsimp only
    rw [lhDomain_vanish c i hi, map_zero]⟩
  map_zero' := lhDomain_ext fun i => by dsimp only; exact map_zero _
  map_add' a b := lhDomain_ext fun i => by dsimp only; exact map_add _ _ _

/-- Restriction `U → U ∩ V`, on the column. -/
def colResWU (mv : MVSequence X U V W) (r n : ℕ) : lhDomain U r n →+ lhDomain W r n where
  toFun c := ⟨fun i => mv.resWU _ ((c : (i : Fin r) → Hmod2 U (n - 2 * (i : ℕ))) i), by
    intro i hi
    dsimp only
    rw [lhDomain_vanish c i hi, map_zero]⟩
  map_zero' := lhDomain_ext fun i => by dsimp only; exact map_zero _
  map_add' a b := lhDomain_ext fun i => by dsimp only; exact map_add _ _ _

/-- Restriction `V → U ∩ V`, on the column. -/
def colResWV (mv : MVSequence X U V W) (r n : ℕ) : lhDomain V r n →+ lhDomain W r n where
  toFun c := ⟨fun i => mv.resWV _ ((c : (i : Fin r) → Hmod2 V (n - 2 * (i : ℕ))) i), by
    intro i hi
    dsimp only
    rw [lhDomain_vanish c i hi, map_zero]⟩
  map_zero' := lhDomain_ext fun i => by dsimp only; exact map_zero _
  map_add' a b := lhDomain_ext fun i => by dsimp only; exact map_add _ _ _

/-- The connecting map on the column.  The `dite` is not a case split in disguise:
where `2i > n` the source entry already vanishes, so both branches agree, and the
branch is there only to supply the degree identity `n - 2i + 1 = n + 1 - 2i`,
which holds precisely when `2i ≤ n`. -/
def colDelta (mv : MVSequence X U V W) (r n : ℕ) :
    lhDomain W r n →+ lhDomain X r (n + 1) where
  toFun c := ⟨fun i =>
      if h : 2 * (i : ℕ) ≤ n then
        cohCast (by omega) (mv.δ _ ((c : (i : Fin r) → Hmod2 W (n - 2 * (i : ℕ))) i))
      else 0, by
    intro i hi
    dsimp only
    rw [dif_neg (by omega)]⟩
  map_zero' := lhDomain_ext fun i => by
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply]
    by_cases h : 2 * (i : ℕ) ≤ n
    · rw [dif_pos h, map_zero, cohCast_zero]
    · rw [dif_neg h]
  map_add' a b := lhDomain_ext fun i => by
    simp only [AddMemClass.coe_add, Pi.add_apply]
    by_cases h : 2 * (i : ℕ) ≤ n
    · rw [dif_pos h, dif_pos h, dif_pos h, map_add, cohCast_add]
    · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

@[simp] theorem colResU_apply (mv : MVSequence X U V W) (r n : ℕ) (c : lhDomain X r n)
    (i : Fin r) :
    ((colResU mv r n c : (i : Fin r) → Hmod2 U (n - 2 * (i : ℕ))) i)
      = mv.resU _ ((c : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) i) := rfl

@[simp] theorem colResV_apply (mv : MVSequence X U V W) (r n : ℕ) (c : lhDomain X r n)
    (i : Fin r) :
    ((colResV mv r n c : (i : Fin r) → Hmod2 V (n - 2 * (i : ℕ))) i)
      = mv.resV _ ((c : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) i) := rfl

@[simp] theorem colResWU_apply (mv : MVSequence X U V W) (r n : ℕ) (c : lhDomain U r n)
    (i : Fin r) :
    ((colResWU mv r n c : (i : Fin r) → Hmod2 W (n - 2 * (i : ℕ))) i)
      = mv.resWU _ ((c : (i : Fin r) → Hmod2 U (n - 2 * (i : ℕ))) i) := rfl

@[simp] theorem colResWV_apply (mv : MVSequence X U V W) (r n : ℕ) (c : lhDomain V r n)
    (i : Fin r) :
    ((colResWV mv r n c : (i : Fin r) → Hmod2 W (n - 2 * (i : ℕ))) i)
      = mv.resWV _ ((c : (i : Fin r) → Hmod2 V (n - 2 * (i : ℕ))) i) := rfl

end

end CharClass
end GroupApproximation
