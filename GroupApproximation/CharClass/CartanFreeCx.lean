import GroupApproximation.CharClass.SteenrodDiagonalTarget

/-!
# Free `F₂`-complexes presented by a degreewise index, and their tensor product

The Cartan comparison needs the tensor square of the singular chain complex and
then the tensor square of *that*.  Doing each by hand would be two long and
nearly identical arguments, so this file does the construction once, for an
abstract complex of free `F₂`-modules presented by its degreewise basis.

The tensor is indexed by `cc-steenrod`'s `PairDeg`, the type of ordered pairs of
degrees with the sum constraint carried as a proposition.  That choice is not
cosmetic: it makes the tensor of the singular complex with itself
*definitionally* their `PairIdx`, so their differential and this one are the same
map, and the fourfold object of the comparison is the tensor of the pair with
itself with no reindexing anywhere.

The differential is the sum of the two per-factor halves.  There are no signs:
in characteristic two the Koszul rule is invisible, which is also why the two
mixed terms of `d ∘ d` cancel against each other rather than against a sign.

## Main results

* `FreeCx` — a complex of free `F₂`-modules, given by index types and a
  differential that squares to zero.
* `TensorIdx`, `tenElt` — the index of the tensor and its bilinear generator.
* `tdL`, `tdR`, `tensorD` — the two halves and the differential.
* `tensorD_tenElt` — the differential on a decomposable element, in closed form.
* `tensorD_tensorD` — **the tensor is a complex.**
-/

namespace GroupApproximation.CharClass

open CategoryTheory

noncomputable section

/-! ## 1. The presentation -/

/-- A chain complex of free `F₂`-modules, presented by its degreewise basis. -/
structure FreeCx where
  /-- The basis of the degree-`k` piece. -/
  ι : ℕ → Type
  /-- The differential. -/
  d : ∀ k : ℕ, (ι (k + 1) →₀ ZMod 2) →ₗ[ZMod 2] (ι k →₀ ZMod 2)
  /-- The differential squares to zero. -/
  d_d : ∀ (k : ℕ) (u : ι (k + 2) →₀ ZMod 2), d k (d (k + 1) u) = 0

variable (A B : FreeCx)

/-- The basis of the degree-`k` piece of the tensor product: a pair of degrees
summing to `k`, and a basis element of each factor in its degree. -/
abbrev TensorIdx (k : ℕ) : Type :=
  Σ p : Steenrod.PairDeg k, A.ι p.val.1 × B.ι p.val.2

/-! ## 2. The bilinear generator -/

/-- `x ⊗ (-)` for a fixed basis element `x` of the first factor. -/
def incR {k : ℕ} (p : Steenrod.PairDeg k) (x : A.ι p.val.1) :
    (B.ι p.val.2 →₀ ZMod 2) →ₗ[ZMod 2] (TensorIdx A B k →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (fun y => (⟨p, (x, y)⟩ : TensorIdx A B k))

@[simp] theorem incR_single {k : ℕ} (p : Steenrod.PairDeg k) (x : A.ι p.val.1)
    (y : B.ι p.val.2) (c : ZMod 2) :
    incR A B p x (Finsupp.single y c) = Finsupp.single (⟨p, (x, y)⟩ : TensorIdx A B k) c := by
  unfold incR
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- `(-) ⊗ v` for a fixed chain `v` of the second factor. -/
noncomputable def tenEltL {k : ℕ} (p : Steenrod.PairDeg k) (v : B.ι p.val.2 →₀ ZMod 2) :
    (A.ι p.val.1 →₀ ZMod 2) →ₗ[ZMod 2] (TensorIdx A B k →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (fun x => incR A B p x v)

/-- **The decomposable element `u ⊗ v`.** -/
noncomputable def tenElt {k : ℕ} (p : Steenrod.PairDeg k)
    (u : A.ι p.val.1 →₀ ZMod 2) (v : B.ι p.val.2 →₀ ZMod 2) : TensorIdx A B k →₀ ZMod 2 :=
  tenEltL A B p v u

theorem tenElt_single_left {k : ℕ} (p : Steenrod.PairDeg k) (x : A.ι p.val.1) (c : ZMod 2)
    (v : B.ι p.val.2 →₀ ZMod 2) :
    tenElt A B p (Finsupp.single x c) v = c • incR A B p x v := by
  show tenEltL A B p v (Finsupp.single x c) = _
  unfold tenEltL
  rw [Finsupp.linearCombination_single]

@[simp] theorem tenElt_single_single {k : ℕ} (p : Steenrod.PairDeg k) (x : A.ι p.val.1)
    (y : B.ι p.val.2) :
    tenElt A B p (Finsupp.single x 1) (Finsupp.single y 1)
      = Finsupp.single (⟨p, (x, y)⟩ : TensorIdx A B k) 1 := by
  rw [tenElt_single_left, incR_single, one_smul]

@[simp] theorem tenElt_zero_left {k : ℕ} (p : Steenrod.PairDeg k)
    (v : B.ι p.val.2 →₀ ZMod 2) : tenElt A B p 0 v = 0 :=
  map_zero (tenEltL A B p v)

theorem tenElt_add_left {k : ℕ} (p : Steenrod.PairDeg k)
    (u u' : A.ι p.val.1 →₀ ZMod 2) (v : B.ι p.val.2 →₀ ZMod 2) :
    tenElt A B p (u + u') v = tenElt A B p u v + tenElt A B p u' v :=
  map_add (tenEltL A B p v) u u'

theorem tenElt_smul_left {k : ℕ} (p : Steenrod.PairDeg k) (c : ZMod 2)
    (u : A.ι p.val.1 →₀ ZMod 2) (v : B.ι p.val.2 →₀ ZMod 2) :
    tenElt A B p (c • u) v = c • tenElt A B p u v :=
  map_smul (tenEltL A B p v) c u

@[simp] theorem tenElt_zero_right {k : ℕ} (p : Steenrod.PairDeg k)
    (u : A.ι p.val.1 →₀ ZMod 2) : tenElt A B p u 0 = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left]
  | add f g hf hg => rw [tenElt_add_left, hf, hg, add_zero]
  | single x c => rw [tenElt_single_left, map_zero, smul_zero]

theorem tenElt_add_right {k : ℕ} (p : Steenrod.PairDeg k)
    (u : A.ι p.val.1 →₀ ZMod 2) (v v' : B.ι p.val.2 →₀ ZMod 2) :
    tenElt A B p u (v + v') = tenElt A B p u v + tenElt A B p u v' := by
  induction u using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, tenElt_zero_left, tenElt_zero_left, add_zero]
  | add f g hf hg =>
      rw [tenElt_add_left, tenElt_add_left, tenElt_add_left, hf, hg]
      abel
  | single x c =>
      rw [tenElt_single_left, tenElt_single_left, tenElt_single_left, map_add, smul_add]

theorem tenElt_smul_right {k : ℕ} (p : Steenrod.PairDeg k) (c : ZMod 2)
    (u : A.ι p.val.1 →₀ ZMod 2) (v : B.ι p.val.2 →₀ ZMod 2) :
    tenElt A B p u (c • v) = c • tenElt A B p u v := by
  induction u using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, tenElt_zero_left, smul_zero]
  | add f g hf hg => rw [tenElt_add_left, tenElt_add_left, hf, hg, smul_add]
  | single x e' =>
      rw [tenElt_single_left, tenElt_single_left, map_smul]
      exact smul_comm _ _ _

/-! ## 3. The two halves of the differential -/

/-- `∂ ⊗ 1`.  The match on the first degree is what keeps it cast-free. -/
noncomputable def tdL (k : ℕ) :
    ∀ (a b : ℕ), a + b = k + 1 → (A.ι a →₀ ZMod 2) → (B.ι b →₀ ZMod 2) →
      (TensorIdx A B k →₀ ZMod 2)
  | 0, _, _, _, _ => 0
  | a' + 1, b, h, u, v =>
      tenElt A B (⟨(a', b), by omega⟩ : Steenrod.PairDeg k) (A.d a' u) v

/-- `1 ⊗ ∂`. -/
noncomputable def tdR (k : ℕ) :
    ∀ (a b : ℕ), a + b = k + 1 → (A.ι a →₀ ZMod 2) → (B.ι b →₀ ZMod 2) →
      (TensorIdx A B k →₀ ZMod 2)
  | _, 0, _, _, _ => 0
  | a, b' + 1, h, u, v =>
      tenElt A B (⟨(a, b'), by omega⟩ : Steenrod.PairDeg k) u (B.d b' v)

@[simp] theorem tdL_zero (k b : ℕ) (h : 0 + b = k + 1) (u : A.ι 0 →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) : tdL A B k 0 b h u v = 0 := rfl

@[simp] theorem tdR_zero (k a : ℕ) (h : a + 0 = k + 1) (u : A.ι a →₀ ZMod 2)
    (v : B.ι 0 →₀ ZMod 2) : tdR A B k a 0 h u v = 0 := rfl

theorem tdL_succ (k a' b : ℕ) (h : a' + 1 + b = k + 1) (u : A.ι (a' + 1) →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tdL A B k (a' + 1) b h u v
      = tenElt A B (⟨(a', b), by omega⟩ : Steenrod.PairDeg k) (A.d a' u) v := rfl

theorem tdR_succ (k a b' : ℕ) (h : a + (b' + 1) = k + 1) (u : A.ι a →₀ ZMod 2)
    (v : B.ι (b' + 1) →₀ ZMod 2) :
    tdR A B k a (b' + 1) h u v
      = tenElt A B (⟨(a, b'), by omega⟩ : Steenrod.PairDeg k) u (B.d b' v) := rfl

/-! ### Bilinearity of the two halves -/

theorem tdL_zero_left (k a b : ℕ) (h : a + b = k + 1) (v : B.ι b →₀ ZMod 2) :
    tdL A B k a b h 0 v = 0 := by
  cases a with
  | zero => rw [tdL_zero]
  | succ a' => rw [tdL_succ, map_zero, tenElt_zero_left]

theorem tdL_add_left (k a b : ℕ) (h : a + b = k + 1) (u u' : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tdL A B k a b h (u + u') v = tdL A B k a b h u v + tdL A B k a b h u' v := by
  cases a with
  | zero => rw [tdL_zero, tdL_zero, tdL_zero, add_zero]
  | succ a' => rw [tdL_succ, tdL_succ, tdL_succ, map_add, tenElt_add_left]

theorem tdL_smul_left (k a b : ℕ) (h : a + b = k + 1) (c : ZMod 2) (u : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tdL A B k a b h (c • u) v = c • tdL A B k a b h u v := by
  cases a with
  | zero => rw [tdL_zero, tdL_zero, smul_zero]
  | succ a' => rw [tdL_succ, tdL_succ, map_smul, tenElt_smul_left]

theorem tdL_add_right (k a b : ℕ) (h : a + b = k + 1) (u : A.ι a →₀ ZMod 2)
    (v v' : B.ι b →₀ ZMod 2) :
    tdL A B k a b h u (v + v') = tdL A B k a b h u v + tdL A B k a b h u v' := by
  cases a with
  | zero => rw [tdL_zero, tdL_zero, tdL_zero, add_zero]
  | succ a' => rw [tdL_succ, tdL_succ, tdL_succ, tenElt_add_right]

theorem tdL_smul_right (k a b : ℕ) (h : a + b = k + 1) (c : ZMod 2) (u : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tdL A B k a b h u (c • v) = c • tdL A B k a b h u v := by
  cases a with
  | zero => rw [tdL_zero, tdL_zero, smul_zero]
  | succ a' => rw [tdL_succ, tdL_succ, tenElt_smul_right]

theorem tdL_zero_right (k a b : ℕ) (h : a + b = k + 1) (u : A.ι a →₀ ZMod 2) :
    tdL A B k a b h u 0 = 0 := by
  cases a with
  | zero => rw [tdL_zero]
  | succ a' => rw [tdL_succ, tenElt_zero_right]

theorem tdR_zero_right (k a b : ℕ) (h : a + b = k + 1) (u : A.ι a →₀ ZMod 2) :
    tdR A B k a b h u 0 = 0 := by
  cases b with
  | zero => rw [tdR_zero]
  | succ b' => rw [tdR_succ, map_zero, tenElt_zero_right]

theorem tdR_zero_left (k a b : ℕ) (h : a + b = k + 1) (v : B.ι b →₀ ZMod 2) :
    tdR A B k a b h 0 v = 0 := by
  cases b with
  | zero => rw [tdR_zero]
  | succ b' => rw [tdR_succ, tenElt_zero_left]

theorem tdR_add_left (k a b : ℕ) (h : a + b = k + 1) (u u' : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tdR A B k a b h (u + u') v = tdR A B k a b h u v + tdR A B k a b h u' v := by
  cases b with
  | zero => rw [tdR_zero, tdR_zero, tdR_zero, add_zero]
  | succ b' => rw [tdR_succ, tdR_succ, tdR_succ, tenElt_add_left]

theorem tdR_smul_left (k a b : ℕ) (h : a + b = k + 1) (c : ZMod 2) (u : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tdR A B k a b h (c • u) v = c • tdR A B k a b h u v := by
  cases b with
  | zero => rw [tdR_zero, tdR_zero, smul_zero]
  | succ b' => rw [tdR_succ, tdR_succ, tenElt_smul_left]

theorem tdR_add_right (k a b : ℕ) (h : a + b = k + 1) (u : A.ι a →₀ ZMod 2)
    (v v' : B.ι b →₀ ZMod 2) :
    tdR A B k a b h u (v + v') = tdR A B k a b h u v + tdR A B k a b h u v' := by
  cases b with
  | zero => rw [tdR_zero, tdR_zero, tdR_zero, add_zero]
  | succ b' => rw [tdR_succ, tdR_succ, tdR_succ, map_add, tenElt_add_right]

theorem tdR_smul_right (k a b : ℕ) (h : a + b = k + 1) (c : ZMod 2) (u : A.ι a →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) :
    tdR A B k a b h u (c • v) = c • tdR A B k a b h u v := by
  cases b with
  | zero => rw [tdR_zero, tdR_zero, smul_zero]
  | succ b' => rw [tdR_succ, tdR_succ, map_smul, tenElt_smul_right]

/-! ## 4. The differential -/

/-- The differential on a basis element. -/
noncomputable def tensorDGen (k : ℕ) (q : TensorIdx A B (k + 1)) :
    TensorIdx A B k →₀ ZMod 2 :=
  tdL A B k q.1.val.1 q.1.val.2 q.1.property
      (Finsupp.single q.2.1 1) (Finsupp.single q.2.2 1)
    + tdR A B k q.1.val.1 q.1.val.2 q.1.property
      (Finsupp.single q.2.1 1) (Finsupp.single q.2.2 1)

/-- **The differential of the tensor product.** -/
noncomputable def tensorD (k : ℕ) :
    (TensorIdx A B (k + 1) →₀ ZMod 2) →ₗ[ZMod 2] (TensorIdx A B k →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (tensorDGen A B k)

@[simp] theorem tensorD_single (k : ℕ) (q : TensorIdx A B (k + 1)) (c : ZMod 2) :
    tensorD A B k (Finsupp.single q c) = c • tensorDGen A B k q := by
  unfold tensorD
  rw [Finsupp.linearCombination_single]

/-- **The differential on a decomposable element**, in closed form. -/
theorem tensorD_tenElt (k a b : ℕ) (h : a + b = k + 1)
    (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    tensorD A B k (tenElt A B (⟨(a, b), h⟩ : Steenrod.PairDeg (k + 1)) u v)
      = tdL A B k a b h u v + tdR A B k a b h u v := by
  induction u using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, map_zero, tdL_zero_left, tdR_zero_left, add_zero]
  | add f g hf hg =>
      rw [tenElt_add_left, map_add, hf, hg, tdL_add_left, tdR_add_left]
      abel
  | single x c =>
      induction v using Finsupp.induction_linear with
      | zero =>
          rw [tenElt_zero_right, map_zero, tdL_zero_right, tdR_zero_right, add_zero]
      | add f g hf hg =>
          rw [tenElt_add_right, map_add, hf, hg, tdL_add_right, tdR_add_right]
          abel
      | single y e =>
          have hq : tensorDGen A B k (⟨⟨(a, b), h⟩, (x, y)⟩ : TensorIdx A B (k + 1))
              = tdL A B k a b h (Finsupp.single x 1) (Finsupp.single y 1)
                + tdR A B k a b h (Finsupp.single x 1) (Finsupp.single y 1) := rfl
          have hc : (Finsupp.single x c : A.ι a →₀ ZMod 2)
              = c • Finsupp.single x (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          have he : (Finsupp.single y e : B.ι b →₀ ZMod 2)
              = e • Finsupp.single y (1 : ZMod 2) := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
          rw [hc, he, tenElt_smul_left, tenElt_smul_right, tenElt_single_single,
            map_smul, map_smul, tensorD_single, one_smul, hq,
            tdL_smul_left, tdL_smul_right, tdR_smul_left, tdR_smul_right,
            smul_add, smul_add]

/-! ## 5. The tensor is a complex -/

/-- The mixed term of `d ∘ d`: one boundary in each factor. -/
noncomputable def tdMix (k : ℕ) :
    ∀ (a b : ℕ), a + b = k + 2 → (A.ι a →₀ ZMod 2) → (B.ι b →₀ ZMod 2) →
      (TensorIdx A B k →₀ ZMod 2)
  | 0, _, _, _, _ => 0
  | _ + 1, 0, _, _, _ => 0
  | a' + 1, b' + 1, h, u, v =>
      tenElt A B (⟨(a', b'), by omega⟩ : Steenrod.PairDeg k) (A.d a' u) (B.d b' v)

@[simp] theorem tdMix_zero (k b : ℕ) (h : 0 + b = k + 2) (u : A.ι 0 →₀ ZMod 2)
    (v : B.ι b →₀ ZMod 2) : tdMix A B k 0 b h u v = 0 := rfl

@[simp] theorem tdMix_succ_zero (k a' : ℕ) (h : a' + 1 + 0 = k + 2)
    (u : A.ι (a' + 1) →₀ ZMod 2) (v : B.ι 0 →₀ ZMod 2) :
    tdMix A B k (a' + 1) 0 h u v = 0 := rfl

theorem tdMix_succ_succ (k a' b' : ℕ) (h : a' + 1 + (b' + 1) = k + 2)
    (u : A.ι (a' + 1) →₀ ZMod 2) (v : B.ι (b' + 1) →₀ ZMod 2) :
    tdMix A B k (a' + 1) (b' + 1) h u v
      = tenElt A B (⟨(a', b'), by omega⟩ : Steenrod.PairDeg k) (A.d a' u) (B.d b' v) := rfl

theorem tensorD_tdL (k a b : ℕ) (h : a + b = k + 2)
    (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    tensorD A B k (tdL A B (k + 1) a b h u v) = tdMix A B k a b h u v := by
  cases a with
  | zero => rw [tdL_zero, map_zero, tdMix_zero]
  | succ a' =>
      rw [tdL_succ, tensorD_tenElt]
      have hL : tdL A B k a' b (by omega) (A.d a' u) v = 0 := by
        cases a' with
        | zero => rw [tdL_zero]
        | succ a'' => rw [tdL_succ, A.d_d, tenElt_zero_left]
      rw [hL, zero_add]
      cases b with
      | zero => rw [tdR_zero, tdMix_succ_zero]
      | succ b' => rw [tdR_succ, tdMix_succ_succ]

theorem tensorD_tdR (k a b : ℕ) (h : a + b = k + 2)
    (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    tensorD A B k (tdR A B (k + 1) a b h u v) = tdMix A B k a b h u v := by
  cases b with
  | zero =>
      rw [tdR_zero, map_zero]
      cases a with
      | zero => rw [tdMix_zero]
      | succ a' => rw [tdMix_succ_zero]
  | succ b' =>
      rw [tdR_succ, tensorD_tenElt]
      have hR : tdR A B k a b' (by omega) u (B.d b' v) = 0 := by
        cases b' with
        | zero => rw [tdR_zero]
        | succ b'' => rw [tdR_succ, B.d_d, tenElt_zero_right]
      rw [hR, add_zero]
      cases a with
      | zero => rw [tdL_zero, tdMix_zero]
      | succ a' => rw [tdL_succ, tdMix_succ_succ]

/-- In characteristic two an element is its own negative. -/
theorem add_self_eq_zero_zmod2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc x + x = (2 : ZMod 2) • x := by rw [two_smul]
    _ = 0 := by rw [h2, zero_smul]

/-- **The tensor product is a complex.**  The two square terms die because each
factor is one, and the two mixed terms are equal and cancel because two is
zero. -/
theorem tensorD_tensorD (k : ℕ) (z : TensorIdx A B (k + 2) →₀ ZMod 2) :
    tensorD A B k (tensorD A B (k + 1) z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | single q c =>
      obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
      have hgen : tensorDGen A B (k + 1) (⟨⟨(a, b), hab⟩, (x, y)⟩ : TensorIdx A B (k + 2))
          = tdL A B (k + 1) a b hab (Finsupp.single x 1) (Finsupp.single y 1)
            + tdR A B (k + 1) a b hab (Finsupp.single x 1) (Finsupp.single y 1) := rfl
      rw [tensorD_single, map_smul, hgen, map_add, tensorD_tdL, tensorD_tdR,
        add_self_eq_zero_zmod2, smul_zero]

end

end GroupApproximation.CharClass
