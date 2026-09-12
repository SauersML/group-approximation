import GroupApproximation.Kazhdan.GHBHyperbolicStokesPolygon
import GroupApproximation.Algebra.LinearIsoperimetricHyperbolic
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# The linear Stokes inequality from fillings of closed chains

Let `S` be a symmetric generating set of a group `Q`, and let `V` be the vertex set of a
complex on which `Q` acts, with adjacency `Adj`, triangles `Tri`, a membership relation
`mem g v` ("the coset `v` contains `g`") and a section `ℓ : V → Q` with
`d_S(g, ℓ v) ≤ M₀` whenever `mem g v`.  Suppose every letter step `g → g s` lies in a
vertex `vert g s`, that two distinct vertices containing a common element are adjacent,
and that the three vertices of a triangle contain a common element.

`ChainFillingBound Adj Tri A` is the area input: along every closed chain
`v :: l ++ [v]` of adjacent vertices, the sum of an antisymmetric integrand whose
triangle sums are at most `C₀` is at most `C₀ A |l ++ [v]|`.  For the coset complex of
`GHB(7)` it is `Systolic.exists_leastDisc_typedLinks`, the typed count `F ≤ 6 B` and
`TriangulatedDisc.abs_boundarySum_le`, at `A = 6`.

`linearStokes_of_chainFillingBound` (H9, H10) proves `LinearStokes S K` with
`K = 12 (2 M₀)² A + 16 (M₀ + 1)²`.  A closed Cayley path `g₀ → g₁ → ⋯ → gₙ = g₀` is joined
by rungs `gₖ → ℓ wₖ` to the chain of vertices `wₖ = vert gₖ sₖ`.  The ladder identity
(`wordSum_sub_chainSum`) writes the difference of the two integrals as a sum of
quadrilaterals of diameter at most `M₀ + 1` (`abs_quadSum_le`, `16 (M₀+1)²` each).
Removing repeated consecutive vertices (`collapse`) turns the vertex chain into a closed
chain of adjacent vertices without changing its integral, and `ChainFillingBound` bounds
that integral, with triangle sums at most `12 (2 M₀)²`.

`isHyperbolicGroup_of_linearStokes` (H11) is Gromov's criterion in this form.
-/

namespace GroupApproximation
namespace GHBHyperbolicStokes

open WordMetric DiscreteStokes

/-! ## Sums along chains and collapsing repeated vertices -/

section Collapse

variable {V : Type*}

/-- The sum of `I` over consecutive pairs of a list. -/
def chainSum (I : V → V → ℤ) : List V → ℤ
  | [] => 0
  | [_] => 0
  | x :: y :: t => I x y + chainSum I (y :: t)

theorem chainSum_nil (I : V → V → ℤ) : chainSum I [] = 0 := by
  simp only [chainSum]

theorem chainSum_singleton (I : V → V → ℤ) (x : V) : chainSum I [x] = 0 := by
  simp only [chainSum]

theorem chainSum_cons_cons (I : V → V → ℤ) (x y : V) (t : List V) :
    chainSum I (x :: y :: t) = I x y + chainSum I (y :: t) := by
  simp only [chainSum]

theorem chainSum_eq_zipWith (I : V → V → ℤ) :
    ∀ l : List V, chainSum I l = (List.zipWith I l l.tail).sum
  | [] => by simp [chainSum_nil]
  | [x] => by simp [chainSum_singleton]
  | x :: y :: t => by
    rw [chainSum_cons_cons, chainSum_eq_zipWith I (y :: t)]
    simp only [List.tail_cons, List.zipWith_cons_cons, List.sum_cons]

variable [DecidableEq V]

/-- Remove repeated consecutive entries. -/
def collapse : List V → List V
  | [] => []
  | [x] => [x]
  | x :: y :: t => if x = y then collapse (y :: t) else x :: collapse (y :: t)

theorem collapse_singleton (x : V) : collapse [x] = [x] := by
  simp only [collapse]

theorem collapse_cons_cons (x y : V) (t : List V) :
    collapse (x :: y :: t) = if x = y then collapse (y :: t) else x :: collapse (y :: t) := by
  simp only [collapse]

/-- Collapsing keeps the first entry. -/
theorem collapse_cons : ∀ (x : V) (t : List V), ∃ t' : List V, collapse (x :: t) = x :: t'
  | x, [] => ⟨[], collapse_singleton x⟩
  | x, y :: t => by
    obtain ⟨t', ht'⟩ := collapse_cons y t
    rw [collapse_cons_cons]
    by_cases h : x = y
    · rw [if_pos h, ht', h]
      exact ⟨t', rfl⟩
    · rw [if_neg h]
      exact ⟨collapse (y :: t), rfl⟩

/-- Collapsing keeps the last entry. -/
theorem getLast?_collapse : ∀ l : List V, (collapse l).getLast? = l.getLast?
  | [] => by simp only [collapse]
  | [x] => by rw [collapse_singleton]
  | x :: y :: t => by
    rw [collapse_cons_cons, List.getLast?_cons_cons, ← getLast?_collapse (y :: t)]
    by_cases h : x = y
    · rw [if_pos h]
    · rw [if_neg h]
      obtain ⟨t', ht'⟩ := collapse_cons y t
      rw [ht', List.getLast?_cons_cons]

/-- Collapsing does not lengthen a list. -/
theorem length_collapse_le : ∀ l : List V, (collapse l).length ≤ l.length
  | [] => by simp only [collapse, le_refl]
  | [x] => by simp only [collapse_singleton, le_refl]
  | x :: y :: t => by
    have ih := length_collapse_le (y :: t)
    rw [collapse_cons_cons]
    by_cases h : x = y
    · rw [if_pos h]
      simp only [List.length_cons] at ih ⊢
      omega
    · rw [if_neg h]
      simp only [List.length_cons] at ih ⊢
      omega

/-- Collapsing does not change a chain sum whose integrand vanishes on the diagonal. -/
theorem chainSum_collapse (I : V → V → ℤ) (hI : ∀ x, I x x = 0) :
    ∀ l : List V, chainSum I (collapse l) = chainSum I l
  | [] => by simp only [collapse]
  | [x] => by rw [collapse_singleton]
  | x :: y :: t => by
    have ih := chainSum_collapse I hI (y :: t)
    rw [collapse_cons_cons, chainSum_cons_cons]
    by_cases h : x = y
    · rw [if_pos h, ih, h, hI, zero_add]
    · rw [if_neg h]
      obtain ⟨t', ht'⟩ := collapse_cons y t
      rw [ht'] at ih ⊢
      rw [chainSum_cons_cons, ih]

/-- A chain for "equal or adjacent" collapses to a chain for adjacency. -/
theorem isChain_collapse {R : V → V → Prop} :
    ∀ l : List V, List.IsChain (fun v w => v = w ∨ R v w) l → List.IsChain R (collapse l)
  | [], _ => by simp only [collapse, List.isChain_nil]
  | [x], _ => by
    rw [collapse_singleton]
    exact List.IsChain.singleton _
  | x :: y :: t, h => by
    rw [List.isChain_cons_cons] at h
    have h1 : x = y ∨ R x y := h.1
    have ih := isChain_collapse (y :: t) h.2
    rw [collapse_cons_cons]
    by_cases hxy : x = y
    · rw [if_pos hxy]
      exact ih
    · rw [if_neg hxy]
      obtain ⟨t', ht'⟩ := collapse_cons y t
      rw [ht'] at ih ⊢
      rw [List.isChain_cons_cons]
      exact ⟨h1.resolve_left hxy, ih⟩

end Collapse

/-! ## The area input -/

section Filling

variable {V : Type*}

/-- **The area input** at constant `A`: along a closed chain `v :: l ++ [v]` of adjacent
vertices, an antisymmetric integrand whose triangle sums are at most `C₀` has boundary sum
at most `C₀ A (|l| + 1)`. -/
def ChainFillingBound (Adj : V → V → Prop) (Tri : V → V → V → Prop) (A : ℕ) : Prop :=
  ∀ (v : V) (l : List V), List.IsChain Adj (v :: l ++ [v]) → l ≠ [] →
    ∀ (I : V → V → ℤ), (∀ x y, I y x = -I x y) → ∀ C₀ : ℕ,
      (∀ x y z, Tri x y z → |I x y + I y z + I z x| ≤ C₀) →
        |(List.zipWith I (v :: l ++ [v]) (v :: l ++ [v]).tail).sum| ≤
          (C₀ : ℤ) * A * (l.length + 1)

variable [DecidableEq V] {Adj : V → V → Prop} {Tri : V → V → V → Prop} {A : ℕ}

/-- **Closed chains with repetitions.**  A closed list along which consecutive entries are
equal or adjacent has integral at most `C₀ A` per step. -/
theorem abs_chainSum_le_of_chainFillingBound (hfill : ChainFillingBound Adj Tri A)
    (I : V → V → ℤ) (hanti : ∀ x y, I y x = -I x y) (C₀ : ℕ)
    (htri : ∀ x y z, Tri x y z → |I x y + I y z + I z x| ≤ C₀) (v : V) (t : List V)
    (hlast : (v :: t).getLast? = some v)
    (hchain : List.IsChain (fun x y => x = y ∨ Adj x y) (v :: t)) :
    |chainSum I (v :: t)| ≤ (C₀ : ℤ) * A * t.length := by
  have hI0 : ∀ x, I x x = 0 := fun x => by linarith [hanti x x]
  have hnonneg : (0 : ℤ) ≤ (C₀ : ℤ) * A * t.length := by positivity
  rw [← chainSum_collapse I hI0]
  obtain ⟨t', ht'⟩ := collapse_cons v t
  have hlen : t'.length ≤ t.length := by
    have h := length_collapse_le (v :: t)
    rw [ht'] at h
    simp only [List.length_cons] at h
    omega
  have hlast' : (v :: t').getLast? = some v := by
    rw [← ht', getLast?_collapse, hlast]
  have hch : List.IsChain Adj (v :: t') := by
    rw [← ht']
    exact isChain_collapse (v :: t) hchain
  rw [ht']
  rcases List.eq_nil_or_concat t' with rfl | ⟨L, u, rfl⟩
  · rw [chainSum_singleton, abs_zero]
    exact hnonneg
  · simp only [List.concat_eq_append] at hlast' hch hlen ⊢
    have hu : u = v := by
      have h : (v :: L ++ [u]).getLast? = some u := List.getLast?_concat
      exact Option.some.inj (h.symm.trans hlast')
    subst hu
    rcases L with _ | ⟨w, L'⟩
    · have h0 : chainSum I [u, u] = 0 := by
        rw [chainSum_cons_cons, chainSum_singleton, hI0, add_zero]
      rw [List.nil_append, h0, abs_zero]
      exact hnonneg
    · have hne : (w :: L') ≠ [] := List.cons_ne_nil w L'
      have hch' : List.IsChain Adj (u :: (w :: L') ++ [u]) := hch
      have hb := hfill u (w :: L') hch' hne I hanti C₀ htri
      rw [← chainSum_eq_zipWith] at hb
      have hlen' : (w :: L').length + 1 ≤ t.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
        omega
      have hC : (0 : ℤ) ≤ (C₀ : ℤ) * A := by positivity
      calc _ ≤ (C₀ : ℤ) * A * ((w :: L').length + 1) := hb
        _ ≤ (C₀ : ℤ) * A * t.length :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hlen') hC

end Filling

/-! ## The ladder along a Cayley path -/

section Ladder

variable {Q V : Type*} [Group Q]

/-- The vertex at the start of the ladder read from `b` along `l`; `v₀` closes it. -/
def headVertex (vert : Q → Q → V) (v₀ : V) (b : Q) : List Q → V
  | [] => v₀
  | x :: _ => vert b x

/-- The vertices of the ladder: one per letter, then the closing vertex `v₀`. -/
def ladderVertices (vert : Q → Q → V) (v₀ : V) : Q → List Q → List V
  | _, [] => [v₀]
  | b, x :: l => vert b x :: ladderVertices vert v₀ (b * x) l

/-- The quadrilaterals between consecutive rungs. -/
def quadSum (vert : Q → Q → V) (ℓ : V → Q) (φ ψ : Q → ℤ) (v₀ : V) : Q → List Q → ℤ
  | _, [] => 0
  | b, x :: l =>
    edgeTerm φ ψ b (b * x) + edgeTerm φ ψ (b * x) (ℓ (headVertex vert v₀ (b * x) l)) +
      edgeTerm φ ψ (ℓ (headVertex vert v₀ (b * x) l)) (ℓ (vert b x)) +
        edgeTerm φ ψ (ℓ (vert b x)) b + quadSum vert ℓ φ ψ v₀ (b * x) l

theorem headVertex_nil (vert : Q → Q → V) (v₀ : V) (b : Q) : headVertex vert v₀ b [] = v₀ :=
  rfl

theorem headVertex_cons (vert : Q → Q → V) (v₀ : V) (b x : Q) (l : List Q) :
    headVertex vert v₀ b (x :: l) = vert b x :=
  rfl

theorem ladderVertices_nil (vert : Q → Q → V) (v₀ : V) (b : Q) :
    ladderVertices vert v₀ b [] = [v₀] :=
  rfl

theorem ladderVertices_cons (vert : Q → Q → V) (v₀ : V) (b x : Q) (l : List Q) :
    ladderVertices vert v₀ b (x :: l) = vert b x :: ladderVertices vert v₀ (b * x) l :=
  rfl

theorem quadSum_nil (vert : Q → Q → V) (ℓ : V → Q) (φ ψ : Q → ℤ) (v₀ : V) (b : Q) :
    quadSum vert ℓ φ ψ v₀ b [] = 0 :=
  rfl

theorem quadSum_cons (vert : Q → Q → V) (ℓ : V → Q) (φ ψ : Q → ℤ) (v₀ : V) (b x : Q)
    (l : List Q) :
    quadSum vert ℓ φ ψ v₀ b (x :: l) =
      edgeTerm φ ψ b (b * x) + edgeTerm φ ψ (b * x) (ℓ (headVertex vert v₀ (b * x) l)) +
        edgeTerm φ ψ (ℓ (headVertex vert v₀ (b * x) l)) (ℓ (vert b x)) +
          edgeTerm φ ψ (ℓ (vert b x)) b + quadSum vert ℓ φ ψ v₀ (b * x) l :=
  rfl

theorem ladderVertices_eq_cons (vert : Q → Q → V) (v₀ : V) :
    ∀ (b : Q) (l : List Q), ∃ rest : List V,
      ladderVertices vert v₀ b l = headVertex vert v₀ b l :: rest
  | _, [] => ⟨[], rfl⟩
  | b, x :: l => ⟨ladderVertices vert v₀ (b * x) l, rfl⟩

theorem length_ladderVertices (vert : Q → Q → V) (v₀ : V) :
    ∀ (b : Q) (l : List Q), (ladderVertices vert v₀ b l).length = l.length + 1
  | _, [] => rfl
  | b, x :: l => by
    rw [ladderVertices_cons, List.length_cons, length_ladderVertices vert v₀ (b * x) l,
      List.length_cons]

theorem getLast?_ladderVertices (vert : Q → Q → V) (v₀ : V) :
    ∀ (b : Q) (l : List Q), (ladderVertices vert v₀ b l).getLast? = some v₀
  | _, [] => rfl
  | b, x :: l => by
    obtain ⟨rest, hrest⟩ := ladderVertices_eq_cons vert v₀ (b * x) l
    have ih := getLast?_ladderVertices vert v₀ (b * x) l
    rw [ladderVertices_cons]
    rw [hrest] at ih ⊢
    rw [List.getLast?_cons_cons, ih]

theorem chainSum_cons_ladderVertices (vert : Q → Q → V) (v₀ : V) (I : V → V → ℤ) (v : V)
    (b : Q) (l : List Q) :
    chainSum I (v :: ladderVertices vert v₀ b l) =
      I v (headVertex vert v₀ b l) + chainSum I (ladderVertices vert v₀ b l) := by
  obtain ⟨rest, hrest⟩ := ladderVertices_eq_cons vert v₀ b l
  rw [hrest, chainSum_cons_cons]

/-- **The ladder identity along a Cayley path.** -/
theorem wordSum_sub_chainSum (vert : Q → Q → V) (ℓ : V → Q) (φ ψ : Q → ℤ) (v₀ : V) :
    ∀ (b : Q) (l : List Q),
      wordSum (id : Q → Q) φ ψ b (trueLetters l) -
          chainSum (fun x y => edgeTerm φ ψ (ℓ x) (ℓ y)) (ladderVertices vert v₀ b l) =
        quadSum vert ℓ φ ψ v₀ b l + edgeTerm φ ψ b (ℓ (headVertex vert v₀ b l)) -
          edgeTerm φ ψ (b * l.prod) (ℓ v₀)
  | b, [] => by
    rw [trueLetters_nil, wordSum_nil, ladderVertices_nil, chainSum_singleton, quadSum_nil,
      headVertex_nil, List.prod_nil, mul_one]
    ring
  | b, x :: l => by
    have ih := wordSum_sub_chainSum vert ℓ φ ψ v₀ (b * x) l
    have h1 := edgeTerm_swap φ ψ (ℓ (headVertex vert v₀ (b * x) l)) (ℓ (vert b x))
    have h2 := edgeTerm_swap φ ψ b (ℓ (vert b x))
    rw [trueLetters_cons, wordSum_cons, letterVal_true, id_eq, ladderVertices_cons,
      quadSum_cons, headVertex_cons, List.prod_cons, chainSum_cons_ladderVertices, ← mul_assoc]
    linarith [ih, h1, h2]

variable {S : Set Q}

/-- **The quadrilaterals are short.**  If every letter lies in `S`, every step lies in its
vertex, sections are within `M₀` of the elements their vertices contain, and the endpoint
lies in `v₀`, then each quadrilateral contributes at most `16 (M₀ + 1)²`. -/
theorem abs_quadSum_le (hS : IsSymmetricGeneratingSet S) (vert : Q → Q → V) (ℓ : V → Q)
    {φ ψ : Q → ℤ} (hφ : ∀ (g s : Q), s ∈ S → |φ (g * s) - φ g| ≤ 1)
    (hψ : ∀ (g s : Q), s ∈ S → |ψ (g * s) - ψ g| ≤ 1) (v₀ : V) (mem : Q → V → Prop)
    {M₀ : ℕ} (hℓ : ∀ g v, mem g v → wordDist S g (ℓ v) ≤ M₀)
    (hvert : ∀ g s, s ∈ S → mem g (vert g s) ∧ mem (g * s) (vert g s)) :
    ∀ (b : Q) (l : List Q), (∀ x ∈ l, x ∈ S) → mem (b * l.prod) v₀ →
      |quadSum vert ℓ φ ψ v₀ b l| ≤ l.length * (16 * ((M₀ + 1 : ℕ) : ℤ) ^ 2)
  | b, [], _, _ => by
    simp only [quadSum_nil, abs_zero, List.length_nil, Nat.cast_zero, zero_mul, le_refl]
  | b, x :: l, hl, hend => by
    have hx : x ∈ S := hl x (List.mem_cons.mpr (Or.inl rfl))
    have hl' : ∀ y ∈ l, y ∈ S := fun y hy => hl y (List.mem_cons.mpr (Or.inr hy))
    have hend' : mem (b * x * l.prod) v₀ := by
      rw [List.prod_cons, ← mul_assoc] at hend
      exact hend
    have ih := abs_quadSum_le hS vert ℓ hφ hψ v₀ mem hℓ hvert (b * x) l hl' hend'
    have hhead : mem (b * x) (headVertex vert v₀ (b * x) l) := by
      cases l with
      | nil =>
        rw [List.prod_nil, mul_one] at hend'
        exact hend'
      | cons y l => exact (hvert (b * x) y (hl' y (List.mem_cons.mpr (Or.inl rfl)))).1
    have d1 : wordDist S b (b * x) ≤ 1 := by
      unfold wordDist
      rw [inv_mul_cancel_left]
      exact wordNorm_le_one_of_mem hx
    have d2 : wordDist S b (ℓ (vert b x)) ≤ M₀ + 1 :=
      (hℓ b _ (hvert b x hx).1).trans (Nat.le_succ M₀)
    have d3 : wordDist S b (ℓ (headVertex vert v₀ (b * x) l)) ≤ M₀ + 1 := by
      have h := wordDist_triangle hS b (b * x) (ℓ (headVertex vert v₀ (b * x) l))
      have h' := hℓ (b * x) _ hhead
      omega
    have hq := abs_quad_edgeTerm_le hS hφ hψ (R := M₀ + 1) (d1.trans (by omega)) d3 d2
    have hsum := abs_add_le
      (edgeTerm φ ψ b (b * x) + edgeTerm φ ψ (b * x) (ℓ (headVertex vert v₀ (b * x) l)) +
        edgeTerm φ ψ (ℓ (headVertex vert v₀ (b * x) l)) (ℓ (vert b x)) +
          edgeTerm φ ψ (ℓ (vert b x)) b)
      (quadSum vert ℓ φ ψ v₀ (b * x) l)
    rw [quadSum_cons, List.length_cons]
    push_cast at hq ih ⊢
    linarith [hsum, hq, ih]

/-- Consecutive vertices of the ladder are equal or adjacent. -/
theorem isChain_ladderVertices (vert : Q → Q → V) (v₀ : V) (mem : Q → V → Prop)
    {Adj : V → V → Prop} (hAdj : ∀ g v w, mem g v → mem g w → v ≠ w → Adj v w)
    (hvert : ∀ g s, s ∈ S → mem g (vert g s) ∧ mem (g * s) (vert g s)) :
    ∀ (b : Q) (l : List Q), (∀ x ∈ l, x ∈ S) → mem (b * l.prod) v₀ →
      List.IsChain (fun v w => v = w ∨ Adj v w) (ladderVertices vert v₀ b l)
  | _, [], _, _ => List.IsChain.singleton _
  | b, x :: l, hl, hend => by
    have hx : x ∈ S := hl x (List.mem_cons.mpr (Or.inl rfl))
    have hl' : ∀ y ∈ l, y ∈ S := fun y hy => hl y (List.mem_cons.mpr (Or.inr hy))
    have hend' : mem (b * x * l.prod) v₀ := by
      rw [List.prod_cons, ← mul_assoc] at hend
      exact hend
    have ih := isChain_ladderVertices vert v₀ mem hAdj hvert (b * x) l hl' hend'
    have hhead : mem (b * x) (headVertex vert v₀ (b * x) l) := by
      cases l with
      | nil =>
        rw [List.prod_nil, mul_one] at hend'
        exact hend'
      | cons y l => exact (hvert (b * x) y (hl' y (List.mem_cons.mpr (Or.inl rfl)))).1
    obtain ⟨rest, hrest⟩ := ladderVertices_eq_cons vert v₀ (b * x) l
    rw [ladderVertices_cons]
    rw [hrest] at ih ⊢
    rw [List.isChain_cons_cons]
    refine ⟨?_, ih⟩
    by_cases e : vert b x = headVertex vert v₀ (b * x) l
    · exact Or.inl e
    · exact Or.inr (hAdj (b * x) _ _ (hvert b x hx).2 hhead e)

/-- **H9–H10: the linear Stokes inequality from fillings of closed chains.** -/
theorem linearStokes_of_chainFillingBound [DecidableEq V] (hS : IsSymmetricGeneratingSet S)
    {Adj : V → V → Prop} {Tri : V → V → V → Prop} {A : ℕ}
    (hfill : ChainFillingBound Adj Tri A) (mem : Q → V → Prop) (ℓ : V → Q) {M₀ : ℕ}
    (hℓ : ∀ g v, mem g v → wordDist S g (ℓ v) ≤ M₀)
    (hAdj : ∀ g v w, mem g v → mem g w → v ≠ w → Adj v w)
    (hTri : ∀ x y z, Tri x y z → ∃ g, mem g x ∧ mem g y ∧ mem g z)
    (vert : Q → Q → V) (hvert : ∀ g s, s ∈ S → mem g (vert g s) ∧ mem (g * s) (vert g s)) :
    LinearStokes S (12 * (2 * M₀) ^ 2 * A + 16 * (M₀ + 1) ^ 2) := by
  intro φ ψ hφ hψ l hl b hprod
  cases l with
  | nil => simp
  | cons x l' =>
    have hx : x ∈ S := hl x (List.mem_cons.mpr (Or.inl rfl))
    have hid := wordSum_sub_chainSum vert ℓ φ ψ (vert b x) b (x :: l')
    rw [hprod, mul_one, headVertex_cons, add_sub_cancel_right, ladderVertices_cons] at hid
    have hend : mem (b * (x :: l').prod) (vert b x) := by
      rw [hprod, mul_one]
      exact (hvert b x hx).1
    have hquad := abs_quadSum_le hS vert ℓ hφ hψ (vert b x) mem hℓ hvert b (x :: l') hl hend
    have hch := isChain_ladderVertices vert (vert b x) mem hAdj hvert b (x :: l') hl hend
    have hlast := getLast?_ladderVertices vert (vert b x) b (x :: l')
    rw [ladderVertices_cons] at hch hlast
    have hanti : ∀ u w : V, edgeTerm φ ψ (ℓ w) (ℓ u) = -edgeTerm φ ψ (ℓ u) (ℓ w) :=
      fun u w => edgeTerm_swap φ ψ (ℓ u) (ℓ w)
    have htri : ∀ u w z, Tri u w z →
        |edgeTerm φ ψ (ℓ u) (ℓ w) + edgeTerm φ ψ (ℓ w) (ℓ z) + edgeTerm φ ψ (ℓ z) (ℓ u)| ≤
          ((12 * (2 * M₀) ^ 2 : ℕ) : ℤ) := by
      intro u w z h
      obtain ⟨g, hgu, hgw, hgz⟩ := hTri u w z h
      have huw : wordDist S (ℓ u) (ℓ w) ≤ 2 * M₀ := by
        have h1 := wordDist_triangle hS (ℓ u) g (ℓ w)
        rw [wordDist_comm hS (ℓ u) g] at h1
        have h2 := hℓ g u hgu
        have h3 := hℓ g w hgw
        omega
      have huz : wordDist S (ℓ u) (ℓ z) ≤ 2 * M₀ := by
        have h1 := wordDist_triangle hS (ℓ u) g (ℓ z)
        rw [wordDist_comm hS (ℓ u) g] at h1
        have h2 := hℓ g u hgu
        have h3 := hℓ g z hgz
        omega
      have hb := abs_triangle_edgeTerm_le hS hφ hψ huw huz
      push_cast at hb ⊢
      exact hb
    have hcs := abs_chainSum_le_of_chainFillingBound hfill
      (fun u w => edgeTerm φ ψ (ℓ u) (ℓ w)) hanti _ htri (vert b x)
      (ladderVertices vert (vert b x) (b * x) l') hlast hch
    rw [length_ladderVertices] at hcs
    have hsum := abs_add_le
      (chainSum (fun u w => edgeTerm φ ψ (ℓ u) (ℓ w))
        (vert b x :: ladderVertices vert (vert b x) (b * x) l'))
      (quadSum vert ℓ φ ψ (vert b x) b (x :: l'))
    have hW : wordSum (id : Q → Q) φ ψ b (trueLetters (x :: l')) =
        chainSum (fun u w => edgeTerm φ ψ (ℓ u) (ℓ w))
          (vert b x :: ladderVertices vert (vert b x) (b * x) l') +
          quadSum vert ℓ φ ψ (vert b x) b (x :: l') := by
      linarith [hid]
    rw [hW]
    simp only [List.length_cons] at hquad ⊢
    push_cast at hcs hquad ⊢
    calc _ ≤ _ := hsum
      _ ≤ 12 * (2 * (M₀ : ℤ)) ^ 2 * A * ((l'.length : ℤ) + 1) +
            ((l'.length : ℤ) + 1) * (16 * ((M₀ : ℤ) + 1) ^ 2) := add_le_add hcs hquad
      _ = (12 * (2 * (M₀ : ℤ)) ^ 2 * A + 16 * ((M₀ : ℤ) + 1) ^ 2) * ((l'.length : ℤ) + 1) := by
        ring

end Ladder

/-! ## Gromov's criterion -/

/-- **H11.**  A finite symmetric generating set satisfying the linear Stokes inequality
makes the group hyperbolic. -/
theorem isHyperbolicGroup_of_linearStokes {Q : Type*} [Group Q] {S : Finset Q}
    (hS : IsSymmetricGeneratingSet (S : Set Q)) {K : ℕ} (hK : LinearStokes (S : Set Q) K) :
    Hyperbolic.IsHyperbolicGroup Q :=
  Hyperbolic.isHyperbolicGroup_of_isSlimTriangles hS
    (isSlimTriangles_of_bowditchH4 hS (Nat.succ_pos _) (bowditchH4_of_linearStokes hS hK))

end GHBHyperbolicStokes
end GroupApproximation

#audit_axioms GroupApproximation.GHBHyperbolicStokes.chainSum_collapse
#audit_axioms GroupApproximation.GHBHyperbolicStokes.abs_chainSum_le_of_chainFillingBound
#audit_axioms GroupApproximation.GHBHyperbolicStokes.wordSum_sub_chainSum
#audit_axioms GroupApproximation.GHBHyperbolicStokes.abs_quadSum_le
#audit_axioms GroupApproximation.GHBHyperbolicStokes.linearStokes_of_chainFillingBound
#audit_axioms GroupApproximation.GHBHyperbolicStokes.isHyperbolicGroup_of_linearStokes
