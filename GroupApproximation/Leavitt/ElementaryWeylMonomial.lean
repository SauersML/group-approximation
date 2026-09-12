import GroupApproximation.Leavitt.ElementaryNoFiniteQuotients
import Mathlib.Data.Matrix.Basis
import Mathlib.Logic.Equiv.Basic

/-!
# Weyl (generalized permutation) elements of the elementary group

The manuscript proof of Lemma `lem:normal-generation-transvection` passes through
a step that had no carrier anywhere in the repository:

> Products of the generalized permutation matrices
> `w_{uv} = e_{uv}(1) e_{vu}(-1) e_{uv}(1)`
> conjugate `e_{jk}(1)` to `e_{uv}(1)` or its inverse for any `u ≠ v`.

This file supplies the carrier, over an arbitrary unital ring `S` and an
arbitrary `Fintype` index `ι`.

**The element.**  `weylUnit u v huv` is the printed word
`e_{uv}(1) e_{vu}(-1) e_{uv}(1)` in `(Matrix ι ι S)ˣ`, and `weyl u v huv` is the
same word inside `elementaryGroup ι S` built from `elGen`
(`GroupApproximation.elGen`, defined in `ElementaryNoFiniteQuotients` as the
elementary matrix of `ElementaryGroup` packaged as a member of the subgroup).
Written out (`weylUnit_val`) it is the identity off the `{u, v}` block and
`[[0, 1], [-1, 0]]` on that block: a signed permutation matrix, which is what
"generalized permutation matrix" means.

**Its conjugation action.**  Conjugation by `w_{uv}` carries each elementary root
to an elementary root at the transposed pair, with a sign:

| position of `e_{pq}(x)`      | `w_{uv} e_{pq}(x) w_{uv}⁻¹` |
| ---------------------------- | --------------------------- |
| `p, q ∉ {u, v}`              | `e_{pq}(x)`                 |
| `p = u`, `q ∉ {u, v}`        | `e_{vq}(-x)`                |
| `p = v`, `q ∉ {u, v}`        | `e_{uq}(x)`                 |
| `q = u`, `p ∉ {u, v}`        | `e_{pv}(-x)`                |
| `q = v`, `p ∉ {u, v}`        | `e_{pu}(x)`                 |
| `p = u`, `q = v`             | `e_{vu}(-x)`                |
| `p = v`, `q = u`             | `e_{uv}(-x)`                |

Those seven cases are `weylUnit_conj_of_notMem`, `weylUnit_conj_of_fst_eq_left`,
`weylUnit_conj_of_fst_eq_right`, `weylUnit_conj_of_snd_eq_left`,
`weylUnit_conj_of_snd_eq_right`, `weylUnit_conj_root` and
`weylUnit_conj_root_symm`; they are exhaustive because `p ≠ q` rules out
`p = q = u` and `p = q = v`.  `weylUnit_conj_swap` assembles them into the
uniform statement: the conjugate is `e_{σp, σq}(x)` **or** `e_{σp, σq}(-x)` for
`σ = Equiv.swap u v`.  The sign alternative is not slack in the bookkeeping — the
first row of the table on which the printed proof relies, `p = u`, `q = v`,
already produces `e_{vu}(-1) = e_{vu}(1)⁻¹`.  This is exactly the manuscript's
"or its inverse".

**The printed conclusion.**  `elGen_one_mem_of_ne` is the sentence the manuscript
needs: if `N ⊴ EL_ι(S)` contains `e_{jk}(1)`, then it contains `e_{uv}(1)` for
every `u ≠ v`.  The proof is the printed one: at most two Weyl conjugations
realise any transposition-pair carrying `(j, k)` to `(u, v)`
(`elGen_one_mem_swap`, `elGen_one_mem_of_source`), and the sign is absorbed by
`N.inv_mem` — the manuscript's "taking inverses if necessary".

**Two remarks on the printed argument.**

1. It is correct as written; no hypothesis is missing and the case analysis
   behind "or its inverse" is complete.
2. This step does **not** need `n ≥ 3`.  Two indices already suffice, because a
   single transposition connects `(j, k)` to `(k, j)` and the target pair is
   reached by at most two.  The lemma's `n ≥ 3` is spent entirely on the
   commutators before and after this step, which need a third index.
   `elGen_one_mem_of_ne` is therefore stated with no cardinality hypothesis.

**Relation to what is already proved.**  `elGen_map_one_eq_one_all_pairs`
(`ElementaryNormalGeneration`) reaches the same conclusion in quotient form by a
different route — the Steinberg source/target moves
`elGen_map_eq_one_source_step` and `elGen_map_eq_one_target_step` — and pays
`3 ≤ Fintype.card ι` for it.  Nothing here is a restatement of that: the route is
the printed one, and the hypothesis is weaker.  The downstream finish is
unchanged and is not repeated here; it is
`elementaryGroup_normal_eq_top_of_elGen_mem` of `ElementaryNormalGeneration`,
which converts `e_{ij}(x) ∈ N` plus a unit sandwich `a x b = 1` into `N = ⊤`.
`ElementaryWeylBridge` records a much narrower fact — one Weyl word in `Fin 3`
over a ring of characteristic two, where the sign disappears — and is not used.
-/

namespace GroupApproximation

namespace ElementaryWeyl

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Ring S]

/-! ### The Weyl element as a matrix unit -/

/-- The **Weyl element** `w_{uv} = e_{uv}(1) e_{vu}(-1) e_{uv}(1)`, the printed
generalized permutation matrix, as a unit of `Matrix ι ι S`.  The factors are
`GroupApproximation.elementaryUnit` of `ElementaryGroup`. -/
def weylUnit (u v : ι) (huv : u ≠ v) : (Matrix ι ι S)ˣ :=
  elementaryUnit u v huv 1 * elementaryUnit v u huv.symm (-1) * elementaryUnit u v huv 1

/-- The inverse of an elementary unit, read off its `inv` field: the definition
`GroupApproximation.elementaryUnit` of `ElementaryGroup` records `1 - E_{ij}(a)`
as the inverse outright. -/
theorem elementaryUnit_val_inv (i j : ι) (h : i ≠ j) (a : S) :
    (((elementaryUnit i j h a)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) =
      1 - Matrix.single i j a := rfl

/-- **The Weyl element written out.**  It is the identity outside the `{u, v}`
block and `[[0, 1], [-1, 0]]` on that block — a signed permutation matrix, which
is the sense in which the manuscript calls `w_{uv}` a generalized permutation
matrix. -/
theorem weylUnit_val (u v : ι) (huv : u ≠ v) :
    (weylUnit (S := S) u v huv : Matrix ι ι S)
      = 1 - Matrix.single u u (1 : S) - Matrix.single v v (1 : S)
          + Matrix.single u v (1 : S) - Matrix.single v u (1 : S) := by
  have hAA : Matrix.single u v (1 : S) * Matrix.single u v (1 : S) = 0 :=
    single_mul_self_eq_zero u v huv 1
  have hAB : Matrix.single u v (1 : S) * Matrix.single v u (1 : S)
      = Matrix.single u u (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hAP : Matrix.single u v (1 : S) * Matrix.single u u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u v u (Ne.symm huv) 1
  have hAQ : Matrix.single u v (1 : S) * Matrix.single v v (1 : S)
      = Matrix.single u v (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hBA : Matrix.single v u (1 : S) * Matrix.single u v (1 : S)
      = Matrix.single v v (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hBB : Matrix.single v u (1 : S) * Matrix.single v u (1 : S) = 0 :=
    single_mul_self_eq_zero v u huv.symm 1
  have hBP : Matrix.single v u (1 : S) * Matrix.single u u (1 : S)
      = Matrix.single v u (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hBQ : Matrix.single v u (1 : S) * Matrix.single v v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v u v huv 1
  have hPA : Matrix.single u u (1 : S) * Matrix.single u v (1 : S)
      = Matrix.single u v (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hPB : Matrix.single u u (1 : S) * Matrix.single v u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u u v huv 1
  have hPP : Matrix.single u u (1 : S) * Matrix.single u u (1 : S)
      = Matrix.single u u (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hPQ : Matrix.single u u (1 : S) * Matrix.single v v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u u v huv 1
  have hQA : Matrix.single v v (1 : S) * Matrix.single u v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v v u (Ne.symm huv) 1
  have hQB : Matrix.single v v (1 : S) * Matrix.single v u (1 : S)
      = Matrix.single v u (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hQP : Matrix.single v v (1 : S) * Matrix.single u u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v v u (Ne.symm huv) 1
  have hQQ : Matrix.single v v (1 : S) * Matrix.single v v (1 : S)
      = Matrix.single v v (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hneg : Matrix.single v u (-1 : S) = - Matrix.single v u (1 : S) :=
    (Matrix.single_neg v u (1 : S)).symm
  have hval : (weylUnit (S := S) u v huv : Matrix ι ι S)
      = (1 + Matrix.single u v (1 : S)) * (1 + Matrix.single v u (-1 : S))
          * (1 + Matrix.single u v (1 : S)) := rfl
  rw [hval, hneg]
  noncomm_ring [hAA, hAB, hAP, hAQ, hBA, hBB, hBP, hBQ,
    hPA, hPB, hPP, hPQ, hQA, hQB, hQP, hQQ]

/-- **The inverse Weyl element written out**: `[[0, -1], [1, 0]]` on the
`{u, v}` block.  Compare `weylUnit_val`; the two differ only in the sign of the
off-diagonal block, which is `w_{uv}⁻¹ = w_{vu}`. -/
theorem weylUnit_inv_val (u v : ι) (huv : u ≠ v) :
    (((weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S)
      = 1 - Matrix.single u u (1 : S) - Matrix.single v v (1 : S)
          - Matrix.single u v (1 : S) + Matrix.single v u (1 : S) := by
  have hAA : Matrix.single u v (1 : S) * Matrix.single u v (1 : S) = 0 :=
    single_mul_self_eq_zero u v huv 1
  have hAB : Matrix.single u v (1 : S) * Matrix.single v u (1 : S)
      = Matrix.single u u (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hAP : Matrix.single u v (1 : S) * Matrix.single u u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u v u (Ne.symm huv) 1
  have hAQ : Matrix.single u v (1 : S) * Matrix.single v v (1 : S)
      = Matrix.single u v (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hBA : Matrix.single v u (1 : S) * Matrix.single u v (1 : S)
      = Matrix.single v v (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hBB : Matrix.single v u (1 : S) * Matrix.single v u (1 : S) = 0 :=
    single_mul_self_eq_zero v u huv.symm 1
  have hBP : Matrix.single v u (1 : S) * Matrix.single u u (1 : S)
      = Matrix.single v u (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hBQ : Matrix.single v u (1 : S) * Matrix.single v v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v u v huv 1
  have hPA : Matrix.single u u (1 : S) * Matrix.single u v (1 : S)
      = Matrix.single u v (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hPB : Matrix.single u u (1 : S) * Matrix.single v u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u u v huv 1
  have hPP : Matrix.single u u (1 : S) * Matrix.single u u (1 : S)
      = Matrix.single u u (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hPQ : Matrix.single u u (1 : S) * Matrix.single v v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u u v huv 1
  have hQA : Matrix.single v v (1 : S) * Matrix.single u v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v v u (Ne.symm huv) 1
  have hQB : Matrix.single v v (1 : S) * Matrix.single v u (1 : S)
      = Matrix.single v u (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hQP : Matrix.single v v (1 : S) * Matrix.single u u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v v u (Ne.symm huv) 1
  have hQQ : Matrix.single v v (1 : S) * Matrix.single v v (1 : S)
      = Matrix.single v v (1 : S) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hneg : Matrix.single v u (-1 : S) = - Matrix.single v u (1 : S) :=
    (Matrix.single_neg v u (1 : S)).symm
  have hval : (((weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S)
      = (1 - Matrix.single u v (1 : S))
          * ((1 - Matrix.single v u (-1 : S)) * (1 - Matrix.single u v (1 : S))) := by
    simp only [weylUnit, mul_inv_rev, Units.val_mul, elementaryUnit_val_inv]
  rw [hval, hneg]
  noncomm_ring [hAA, hAB, hAP, hAQ, hBA, hBB, hBP, hBQ,
    hPA, hPB, hPP, hPQ, hQA, hQB, hQP, hQQ]

/-! ### The two halves of the conjugation

`w_{uv}` acts on the left by the signed transposition `e_u ↦ -e_v`, `e_v ↦ e_u`,
and `w_{uv}⁻¹` acts on the right by `e_u^T ↦ -e_v^T`, `e_v^T ↦ e_u^T`.  Each of
the six lemmas below is one entry of that description, phrased on a single
matrix unit `E_{pq}(x)`; the free index is arbitrary, so the lemmas apply to the
diagonal units that appear in the two `p, q ∈ {u, v}` cases as well. -/

/-- Left action, row untouched: `w_{uv} E_{pq}(x) = E_{pq}(x)` for `p ∉ {u,v}`. -/
theorem weylUnit_val_mul_single_of_ne (u v : ι) (huv : u ≠ v) {p : ι}
    (hpu : p ≠ u) (hpv : p ≠ v) (q : ι) (x : S) :
    (weylUnit (S := S) u v huv : Matrix ι ι S) * Matrix.single p q x
      = Matrix.single p q x := by
  have h1 : Matrix.single u u (1 : S) * Matrix.single p q x = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u u p (Ne.symm hpu) x
  have h2 : Matrix.single v v (1 : S) * Matrix.single p q x = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v v p (Ne.symm hpv) x
  have h3 : Matrix.single u v (1 : S) * Matrix.single p q x = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u v p (Ne.symm hpv) x
  have h4 : Matrix.single v u (1 : S) * Matrix.single p q x = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v u p (Ne.symm hpu) x
  rw [weylUnit_val]
  noncomm_ring [h1, h2, h3, h4]

/-- Left action on the `u` row: `w_{uv} E_{uq}(x) = -E_{vq}(x)`.  This is the
sign the manuscript's "or its inverse" comes from. -/
theorem weylUnit_val_mul_single_fst (u v : ι) (huv : u ≠ v) (q : ι) (x : S) :
    (weylUnit (S := S) u v huv : Matrix ι ι S) * Matrix.single u q x
      = - Matrix.single v q x := by
  have h1 : Matrix.single u u (1 : S) * Matrix.single u q x = Matrix.single u q x := by
    rw [Matrix.single_mul_single_same, one_mul]
  have h2 : Matrix.single v v (1 : S) * Matrix.single u q x = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v v u (Ne.symm huv) x
  have h3 : Matrix.single u v (1 : S) * Matrix.single u q x = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u v u (Ne.symm huv) x
  have h4 : Matrix.single v u (1 : S) * Matrix.single u q x = Matrix.single v q x := by
    rw [Matrix.single_mul_single_same, one_mul]
  rw [weylUnit_val]
  noncomm_ring [h1, h2, h3, h4]

/-- Left action on the `v` row: `w_{uv} E_{vq}(x) = E_{uq}(x)`, with no sign. -/
theorem weylUnit_val_mul_single_snd (u v : ι) (huv : u ≠ v) (q : ι) (x : S) :
    (weylUnit (S := S) u v huv : Matrix ι ι S) * Matrix.single v q x
      = Matrix.single u q x := by
  have h1 : Matrix.single u u (1 : S) * Matrix.single v q x = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u u v huv x
  have h2 : Matrix.single v v (1 : S) * Matrix.single v q x = Matrix.single v q x := by
    rw [Matrix.single_mul_single_same, one_mul]
  have h3 : Matrix.single u v (1 : S) * Matrix.single v q x = Matrix.single u q x := by
    rw [Matrix.single_mul_single_same, one_mul]
  have h4 : Matrix.single v u (1 : S) * Matrix.single v q x = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v u v huv x
  rw [weylUnit_val]
  noncomm_ring [h1, h2, h3, h4]

/-- Right action, column untouched: `E_{pq}(x) w_{uv}⁻¹ = E_{pq}(x)` for
`q ∉ {u,v}`. -/
theorem single_mul_weylUnit_inv_val_of_ne (u v : ι) (huv : u ≠ v) (p : ι) {q : ι}
    (hqu : q ≠ u) (hqv : q ≠ v) (x : S) :
    Matrix.single p q x *
        (((weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S)
      = Matrix.single p q x := by
  have h1 : Matrix.single p q x * Matrix.single u u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := x) p q u hqu 1
  have h2 : Matrix.single p q x * Matrix.single v v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := x) p q v hqv 1
  have h3 : Matrix.single p q x * Matrix.single u v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := x) p q u hqu 1
  have h4 : Matrix.single p q x * Matrix.single v u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := x) p q v hqv 1
  rw [weylUnit_inv_val]
  noncomm_ring [h1, h2, h3, h4]

/-- Right action on the `u` column: `E_{pu}(x) w_{uv}⁻¹ = -E_{pv}(x)`. -/
theorem single_mul_weylUnit_inv_val_fst (u v : ι) (huv : u ≠ v) (p : ι) (x : S) :
    Matrix.single p u x *
        (((weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S)
      = - Matrix.single p v x := by
  have h1 : Matrix.single p u x * Matrix.single u u (1 : S) = Matrix.single p u x := by
    rw [Matrix.single_mul_single_same, mul_one]
  have h2 : Matrix.single p u x * Matrix.single v v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := x) p u v huv 1
  have h3 : Matrix.single p u x * Matrix.single u v (1 : S) = Matrix.single p v x := by
    rw [Matrix.single_mul_single_same, mul_one]
  have h4 : Matrix.single p u x * Matrix.single v u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := x) p u v huv 1
  rw [weylUnit_inv_val]
  noncomm_ring [h1, h2, h3, h4]

/-- Right action on the `v` column: `E_{pv}(x) w_{uv}⁻¹ = E_{pu}(x)`, with no
sign. -/
theorem single_mul_weylUnit_inv_val_snd (u v : ι) (huv : u ≠ v) (p : ι) (x : S) :
    Matrix.single p v x *
        (((weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S)
      = Matrix.single p u x := by
  have h1 : Matrix.single p v x * Matrix.single u u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := x) p v u (Ne.symm huv) 1
  have h2 : Matrix.single p v x * Matrix.single v v (1 : S) = Matrix.single p v x := by
    rw [Matrix.single_mul_single_same, mul_one]
  have h3 : Matrix.single p v x * Matrix.single u v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := x) p v u (Ne.symm huv) 1
  have h4 : Matrix.single p v x * Matrix.single v u (1 : S) = Matrix.single p u x := by
    rw [Matrix.single_mul_single_same, mul_one]
  rw [weylUnit_inv_val]
  noncomm_ring [h1, h2, h3, h4]

/-! ### Conjugation of an elementary root by a Weyl element -/

/-- Conjugation of `e_{pq}(x) = 1 + E_{pq}(x)` is the identity plus the
conjugate of `E_{pq}(x)`: the constant term is `w_{uv} w_{uv}⁻¹ = 1`. -/
theorem weylUnit_conj_val (u v : ι) (huv : u ≠ v) (p q : ι) (hpq : p ≠ q) (x : S) :
    ((weylUnit (S := S) u v huv * elementaryUnit p q hpq x
        * (weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S)
      = 1 + (weylUnit (S := S) u v huv : Matrix ι ι S) * Matrix.single p q x
          * (((weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) := by
  have hval : ((weylUnit (S := S) u v huv * elementaryUnit p q hpq x
      * (weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S)
      = (weylUnit (S := S) u v huv : Matrix ι ι S) * (1 + Matrix.single p q x)
          * (((weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) := rfl
  rw [hval, mul_add, mul_one, add_mul, Units.mul_inv]

/-- The bridge from a matrix-unit computation to a statement about elementary
roots: if conjugation carries `E_{pq}(x)` to `E_{p'q'}(y)`, it carries
`e_{pq}(x)` to `e_{p'q'}(y)`. -/
theorem weylUnit_conj_of_single (u v : ι) (huv : u ≠ v) {p q : ι} (hpq : p ≠ q)
    {p' q' : ι} (hp'q' : p' ≠ q') {x y : S}
    (h : (weylUnit (S := S) u v huv : Matrix ι ι S) * Matrix.single p q x
          * (((weylUnit (S := S) u v huv)⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) =
        Matrix.single p' q' y) :
    weylUnit (S := S) u v huv * elementaryUnit p q hpq x
        * (weylUnit (S := S) u v huv)⁻¹
      = elementaryUnit p' q' hp'q' y := by
  apply Units.ext
  rw [weylUnit_conj_val u v huv p q hpq x, h]
  rfl

/-- **Case `p, q ∉ {u, v}`.**  `w_{uv}` commutes with roots disjoint from its
block. -/
theorem weylUnit_conj_of_notMem (u v : ι) (huv : u ≠ v) {p q : ι} (hpq : p ≠ q)
    (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) (x : S) :
    weylUnit (S := S) u v huv * elementaryUnit p q hpq x
        * (weylUnit (S := S) u v huv)⁻¹
      = elementaryUnit p q hpq x :=
  weylUnit_conj_of_single u v huv hpq hpq (by
    rw [weylUnit_val_mul_single_of_ne u v huv hpu hpv q x,
      single_mul_weylUnit_inv_val_of_ne u v huv p hqu hqv x])

/-- **Case `p = u`, `q ∉ {u, v}`**: `w_{uv} e_{uq}(x) w_{uv}⁻¹ = e_{vq}(-x)`. -/
theorem weylUnit_conj_of_fst_eq_left (u v : ι) (huv : u ≠ v) {q : ι}
    (huq : u ≠ q) (hvq : v ≠ q) (hqu : q ≠ u) (hqv : q ≠ v) (x : S) :
    weylUnit (S := S) u v huv * elementaryUnit u q huq x
        * (weylUnit (S := S) u v huv)⁻¹
      = elementaryUnit v q hvq (-x) :=
  weylUnit_conj_of_single u v huv huq hvq (by
    rw [weylUnit_val_mul_single_fst u v huv q x, neg_mul,
      single_mul_weylUnit_inv_val_of_ne u v huv v hqu hqv x, Matrix.single_neg])

/-- **Case `p = v`, `q ∉ {u, v}`**: `w_{uv} e_{vq}(x) w_{uv}⁻¹ = e_{uq}(x)`, with
no sign. -/
theorem weylUnit_conj_of_fst_eq_right (u v : ι) (huv : u ≠ v) {q : ι}
    (huq : u ≠ q) (hvq : v ≠ q) (hqu : q ≠ u) (hqv : q ≠ v) (x : S) :
    weylUnit (S := S) u v huv * elementaryUnit v q hvq x
        * (weylUnit (S := S) u v huv)⁻¹
      = elementaryUnit u q huq x :=
  weylUnit_conj_of_single u v huv hvq huq (by
    rw [weylUnit_val_mul_single_snd u v huv q x,
      single_mul_weylUnit_inv_val_of_ne u v huv u hqu hqv x])

/-- **Case `q = u`, `p ∉ {u, v}`**: `w_{uv} e_{pu}(x) w_{uv}⁻¹ = e_{pv}(-x)`. -/
theorem weylUnit_conj_of_snd_eq_left (u v : ι) (huv : u ≠ v) {p : ι}
    (hpu : p ≠ u) (hpv : p ≠ v) (x : S) :
    weylUnit (S := S) u v huv * elementaryUnit p u hpu x
        * (weylUnit (S := S) u v huv)⁻¹
      = elementaryUnit p v hpv (-x) :=
  weylUnit_conj_of_single u v huv hpu hpv (by
    rw [weylUnit_val_mul_single_of_ne u v huv hpu hpv u x,
      single_mul_weylUnit_inv_val_fst u v huv p x, Matrix.single_neg])

/-- **Case `q = v`, `p ∉ {u, v}`**: `w_{uv} e_{pv}(x) w_{uv}⁻¹ = e_{pu}(x)`, with
no sign. -/
theorem weylUnit_conj_of_snd_eq_right (u v : ι) (huv : u ≠ v) {p : ι}
    (hpu : p ≠ u) (hpv : p ≠ v) (x : S) :
    weylUnit (S := S) u v huv * elementaryUnit p v hpv x
        * (weylUnit (S := S) u v huv)⁻¹
      = elementaryUnit p u hpu x :=
  weylUnit_conj_of_single u v huv hpv hpu (by
    rw [weylUnit_val_mul_single_of_ne u v huv hpu hpv v x,
      single_mul_weylUnit_inv_val_snd u v huv p x])

/-- **Case `p = u`, `q = v`**: `w_{uv} e_{uv}(x) w_{uv}⁻¹ = e_{vu}(-x)`.  Taking
`x = 1` this is the manuscript's "or its inverse" in its purest form: one Weyl
conjugation already leaves the set of unit roots only up to a sign. -/
theorem weylUnit_conj_root (u v : ι) (huv : u ≠ v) (x : S) :
    weylUnit (S := S) u v huv * elementaryUnit u v huv x
        * (weylUnit (S := S) u v huv)⁻¹
      = elementaryUnit v u huv.symm (-x) :=
  weylUnit_conj_of_single u v huv huv huv.symm (by
    rw [weylUnit_val_mul_single_fst u v huv v x, neg_mul,
      single_mul_weylUnit_inv_val_snd u v huv v x, Matrix.single_neg])

/-- **Case `p = v`, `q = u`**: `w_{uv} e_{vu}(x) w_{uv}⁻¹ = e_{uv}(-x)`. -/
theorem weylUnit_conj_root_symm (u v : ι) (huv : u ≠ v) (x : S) :
    weylUnit (S := S) u v huv * elementaryUnit v u huv.symm x
        * (weylUnit (S := S) u v huv)⁻¹
      = elementaryUnit u v huv (-x) :=
  weylUnit_conj_of_single u v huv huv.symm huv (by
    rw [weylUnit_val_mul_single_snd u v huv u x,
      single_mul_weylUnit_inv_val_fst u v huv u x, Matrix.single_neg])

/-- **The conjugation action of one Weyl element, uniformly.**  Conjugation by
`w_{uv}` carries `e_{pq}(x)` to `e_{σp, σq}(x)` **or** to `e_{σp, σq}(-x)`, where
`σ = Equiv.swap u v` is the transposition `w_{uv}` induces on indices.  The
disjunction is the manuscript's "or its inverse"; it cannot be removed, since
`weylUnit_conj_root` realises the second alternative. -/
theorem weylUnit_conj_swap (u v : ι) (huv : u ≠ v) {p q : ι} (hpq : p ≠ q)
    {p' q' : ι} (hp : Equiv.swap u v p = p') (hq : Equiv.swap u v q = q')
    (hp'q' : p' ≠ q') (x : S) :
    weylUnit (S := S) u v huv * elementaryUnit p q hpq x
          * (weylUnit (S := S) u v huv)⁻¹
        = elementaryUnit p' q' hp'q' x
      ∨ weylUnit (S := S) u v huv * elementaryUnit p q hpq x
          * (weylUnit (S := S) u v huv)⁻¹
        = elementaryUnit p' q' hp'q' (-x) := by
  by_cases hpu : p = u
  · subst hpu
    -- `p` plays the role of `u`; the row index is sent to `v`.
    rw [Equiv.swap_apply_left] at hp
    subst hp
    by_cases hqv : q = v
    · subst hqv
      rw [Equiv.swap_apply_right] at hq
      subst hq
      exact Or.inr (weylUnit_conj_root _ _ huv x)
    · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hpq) hqv] at hq
      subst hq
      exact Or.inr (weylUnit_conj_of_fst_eq_left _ _ huv hpq hp'q' (Ne.symm hpq) hqv x)
  · by_cases hpv : p = v
    · subst hpv
      -- `p` plays the role of `v`; the row index is sent to `u`.
      rw [Equiv.swap_apply_right] at hp
      subst hp
      by_cases hqu : q = u
      · subst hqu
        rw [Equiv.swap_apply_left] at hq
        subst hq
        exact Or.inr (weylUnit_conj_root_symm _ _ huv x)
      · rw [Equiv.swap_apply_of_ne_of_ne hqu (Ne.symm hpq)] at hq
        subst hq
        exact Or.inl (weylUnit_conj_of_fst_eq_right _ _ huv hp'q' hpq hqu (Ne.symm hpq) x)
    · rw [Equiv.swap_apply_of_ne_of_ne hpu hpv] at hp
      subst hp
      by_cases hqu : q = u
      · subst hqu
        rw [Equiv.swap_apply_left] at hq
        subst hq
        exact Or.inr (weylUnit_conj_of_snd_eq_left _ _ huv hpu hpv x)
      · by_cases hqv : q = v
        · subst hqv
          rw [Equiv.swap_apply_right] at hq
          subst hq
          exact Or.inl (weylUnit_conj_of_snd_eq_right _ _ huv hpu hpv x)
        · rw [Equiv.swap_apply_of_ne_of_ne hqu hqv] at hq
          subst hq
          exact Or.inl (weylUnit_conj_of_notMem _ _ huv hpq hpu hpv hqu hqv x)

/-! ### The Weyl element inside `EL_ι(S)`, and the printed conclusion -/

/-- The **Weyl element of `EL_ι(S)`**: the printed word
`w_{uv} = e_{uv}(1) e_{vu}(-1) e_{uv}(1)` written with
`GroupApproximation.elGen` of `ElementaryNoFiniteQuotients`, so that it is a
member of `elementaryGroup ι S` by construction. -/
def weyl (u v : ι) (huv : u ≠ v) : elementaryGroup ι S :=
  elGen u v huv 1 * elGen v u huv.symm (-1) * elGen u v huv 1

/-- `weyl` and `weylUnit` are the same word: `elGen` is `elementaryUnit`
packaged into the subgroup, so the underlying units agree. -/
theorem weyl_val (u v : ι) (huv : u ≠ v) :
    ((weyl (S := S) u v huv : elementaryGroup ι S) : (Matrix ι ι S)ˣ)
      = weylUnit (S := S) u v huv := rfl

/-- The inverse of an elementary root negates its coefficient.  Stated here
rather than imported so that this file depends only on
`ElementaryNoFiniteQuotients`; `RowAnnihilatorTransvection.elGen_inv` records the
same identity for its own consumers. -/
theorem elGen_neg_eq_inv (i j : ι) (h : i ≠ j) (a : S) :
    elGen (R := S) i j h (-a) = (elGen i j h a)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [elGen_mul]
  simp

/-- **The conjugation action, inside `EL_ι(S)`.**  The `elGen` reading of
`weylUnit_conj_swap`. -/
theorem weyl_conj_elGen (u v : ι) (huv : u ≠ v) {p q : ι} (hpq : p ≠ q)
    {p' q' : ι} (hp : Equiv.swap u v p = p') (hq : Equiv.swap u v q = q')
    (hp'q' : p' ≠ q') (x : S) :
    weyl (S := S) u v huv * elGen p q hpq x * (weyl (S := S) u v huv)⁻¹
        = elGen p' q' hp'q' x
      ∨ weyl (S := S) u v huv * elGen p q hpq x * (weyl (S := S) u v huv)⁻¹
        = elGen p' q' hp'q' (-x) := by
  have hval : ((weyl (S := S) u v huv * elGen p q hpq x
        * (weyl (S := S) u v huv)⁻¹ : elementaryGroup ι S) : (Matrix ι ι S)ˣ)
      = weylUnit (S := S) u v huv * elementaryUnit p q hpq x
          * (weylUnit (S := S) u v huv)⁻¹ := rfl
  rcases weylUnit_conj_swap u v huv hpq hp hq hp'q' x with h | h
  · exact Or.inl (Subtype.ext (hval.trans h))
  · exact Or.inr (Subtype.ext (hval.trans h))

/-- **One Weyl conjugation transports a unit root through a normal subgroup.**
This is the manuscript's "Normality of `N`, and taking inverses if necessary":
the sign alternative of `weyl_conj_elGen` is absorbed by `N.inv_mem`, because
`e_{p'q'}(-1)` is the inverse of `e_{p'q'}(1)`. -/
theorem elGen_one_mem_swap (N : Subgroup (elementaryGroup ι S)) [hN : N.Normal]
    {a b : ι} (hab : a ≠ b) {p q : ι} (hpq : p ≠ q)
    {p' q' : ι} (hp : Equiv.swap a b p = p') (hq : Equiv.swap a b q = q')
    (hp'q' : p' ≠ q') (hmem : elGen p q hpq (1 : S) ∈ N) :
    elGen p' q' hp'q' (1 : S) ∈ N := by
  have hconj : weyl (S := S) a b hab * elGen p q hpq (1 : S)
      * (weyl (S := S) a b hab)⁻¹ ∈ N := hN.conj_mem _ hmem _
  rcases weyl_conj_elGen a b hab hpq hp hq hp'q' (1 : S) with h | h
  · rwa [h] at hconj
  · rw [h] at hconj
    have hinv := N.inv_mem hconj
    rwa [← elGen_neg_eq_inv, neg_neg] at hinv

/-- **Moving the target index.**  From `e_{uk}(1) ∈ N` one reaches `e_{uv}(1) ∈ N`
for every `v ≠ u`, by one conjugation with `w_{kv}`, which fixes `u` and carries
`k` to `v`. -/
theorem elGen_one_mem_of_source (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    {u k : ι} (huk : u ≠ k) (hmem : elGen u k huk (1 : S) ∈ N)
    {v : ι} (huv : u ≠ v) : elGen u v huv (1 : S) ∈ N := by
  by_cases hkv : k = v
  · subst hkv
    exact hmem
  · exact elGen_one_mem_swap N hkv huk
      (Equiv.swap_apply_of_ne_of_ne huk huv) (Equiv.swap_apply_left k v) huv hmem

/-- **The printed conclusion.**  "Products of the generalized permutation
matrices `w_{uv} = e_{uv}(1) e_{vu}(-1) e_{uv}(1)` conjugate `e_{jk}(1)` to
`e_{uv}(1)` or its inverse for any `u ≠ v`.  Normality of `N`, and taking
inverses if necessary, therefore gives `e_{uv}(1) ∈ N` for every `u ≠ v`."

At most two Weyl conjugations are used: `w_{ju}` moves the source index onto `u`,
and one more moves the target index onto `v`.  No cardinality hypothesis is
needed — the manuscript's `n ≥ 3` is spent on the commutators surrounding this
step, not on the step itself.  The downstream finish is
`elementaryGroup_normal_eq_top_of_elGen_mem` of `ElementaryNormalGeneration` and
is not repeated here. -/
theorem elGen_one_mem_of_ne (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    {j k : ι} (hjk : j ≠ k) (hmem : elGen j k hjk (1 : S) ∈ N)
    {u v : ι} (huv : u ≠ v) : elGen u v huv (1 : S) ∈ N := by
  by_cases hju : j = u
  · subst hju
    exact elGen_one_mem_of_source N hjk hmem huv
  · by_cases hku : k = u
    · subst hku
      exact elGen_one_mem_of_source N (Ne.symm hjk)
        (elGen_one_mem_swap N hju hjk (Equiv.swap_apply_left j k)
          (Equiv.swap_apply_right j k) (Ne.symm hjk) hmem) huv
    · exact elGen_one_mem_of_source N (Ne.symm hku)
        (elGen_one_mem_swap N hju hjk (Equiv.swap_apply_left j u)
          (Equiv.swap_apply_of_ne_of_ne (Ne.symm hjk) hku) (Ne.symm hku) hmem) huv

end ElementaryWeyl

end GroupApproximation
