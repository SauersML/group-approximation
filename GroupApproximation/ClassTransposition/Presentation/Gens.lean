import GroupApproximation.ClassTransposition.Presentation.Comb

/-!
# The finite presentation of `CT_P(ℤ)`: generators and relators

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §3).

Positions are `1, 2, …` (the research node's positions); a move at box `i` (0-based) of a list of
`n` boxes has position `i + 1`, and box `n - 1` is the tail.

* Generator *types* (`Ty P`): `X p` (split a non-tail box by `p ∈ P ∪ {2}`), `Y p` (split the
  tail by `p ∈ P`), `π` (swap two non-tail boxes) and `ρ` (swap the last non-tail box with the
  tail).
* The finitely many generators are the types at positions 1 and 2 (`Gen P = Ty P × Bool`).
  The generator of type `t` at position `j ≥ 3` is `s⁻¹ g s` with `s = X_{1,2}` (the definitions
  (D), `gF`).
* A move `m` at level `n` (a list of `n` boxes) has the free-group element `hatF P m n`, and a
  word has `toFree P n w`.
* The relators are the instances of the relation families (a)–(d) of Fact O at levels and
  parameters below a bound (`Inst`, `relSet`). There are finitely many (`relSet_finite`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

/-- The primes `P ∪ {2}`. -/
def P' (P : Set ℕ) : Set ℕ := insert 2 P

theorem two_mem (P : Set ℕ) : 2 ∈ P' P := Set.mem_insert _ _

/-- Generator types: `X p`, `Y p`, `π` (`false`), `ρ` (`true`). -/
abbrev Ty (P : Set ℕ) : Type := ↥(P' P) ⊕ ↥P ⊕ Bool

/-- The generators: a type at position 1 (`false`) or 2 (`true`). -/
abbrev Gen (P : Set ℕ) : Type := Ty P × Bool

variable {P : Set ℕ}

/-- The shift `s = X_{1,2}`. -/
def sF (P : Set ℕ) : FreeGroup (Gen P) := FreeGroup.of (Sum.inl ⟨2, two_mem P⟩, false)

/-- The generator of type `t` at position `j`; positions `≥ 3` are defined by the shift. -/
def gF (t : Ty P) : ℕ → FreeGroup (Gen P)
  | 0 => 1
  | 1 => FreeGroup.of (t, false)
  | 2 => FreeGroup.of (t, true)
  | j + 3 => (sF P)⁻¹ * gF t (j + 2) * sF P

theorem gF_succ (t : Ty P) {j : ℕ} (hj : 2 ≤ j) : gF t (j + 1) = (sF P)⁻¹ * gF t j * sF P := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  rfl

/-- The level after a move: a split of an existing box by `p` adds `p - 1` boxes. -/
def Move.lev : Move → ℕ → ℕ
  | .split i p, n => if i < n then n + p - 1 else n
  | .swap _, n => n

open Classical in
/-- The free-group element of a move at level `n`. -/
noncomputable def hatF (P : Set ℕ) : Move → ℕ → FreeGroup (Gen P)
  | .split i p, n =>
    if i + 1 < n then (if hp : p ∈ P' P then gF (Sum.inl ⟨p, hp⟩) (i + 1) else 1)
    else if i + 1 = n ∧ p ≠ 2 then (if hp : p ∈ P then gF (Sum.inr (Sum.inl ⟨p, hp⟩)) (i + 1) else 1)
    else 1
  | .swap k, n =>
    if k + 2 < n then gF (Sum.inr (Sum.inr false)) (k + 1)
    else if k + 2 = n then gF (Sum.inr (Sum.inr true)) (k + 1) else 1

/-- The free-group element of a word at level `n`. -/
noncomputable def toFree (P : Set ℕ) : ℕ → List Move → FreeGroup (Gen P)
  | _, [] => 1
  | n, m :: w => hatF P m n * toFree P (m.lev n) w

/-- The level after a word. -/
def levW : ℕ → List Move → ℕ
  | n, [] => n
  | n, m :: w => levW (m.lev n) w

@[simp] theorem toFree_nil (n : ℕ) : toFree P n [] = 1 := rfl

theorem toFree_cons (n : ℕ) (m : Move) (w : List Move) :
    toFree P n (m :: w) = hatF P m n * toFree P (m.lev n) w := rfl

@[simp] theorem levW_nil (n : ℕ) : levW n [] = n := rfl

theorem levW_cons (n : ℕ) (m : Move) (w : List Move) : levW n (m :: w) = levW (m.lev n) w := rfl

theorem toFree_append : ∀ (n : ℕ) (u v : List Move),
    toFree P n (u ++ v) = toFree P n u * toFree P (levW n u) v
  | n, [], v => by rw [List.nil_append, toFree_nil, levW_nil, one_mul]
  | n, m :: u, v => by
    rw [List.cons_append, toFree_cons, toFree_cons, toFree_append (m.lev n) u v, levW_cons,
      mul_assoc]

/-! ### The relation families -/

/-- The `p` children of box `i`, each split by `q`, left to right. -/
def layer (i p q : ℕ) : List Move := (List.range p).map fun t => .split (i + t * q) q

/-- Swap words at an offset. -/
def swaps (i : ℕ) (w : List ℕ) : List Move := w.map fun k => .swap (i + k)

open Classical in
/-- A swap word reordering the `pq` grandchildren of a `q`-then-`p` split into the order of the
`p`-then-`q` split (the colour exchange). -/
noncomputable def crtWord (p q : ℕ) : List ℕ :=
  if h : ∃ w : List ℕ, (∀ k ∈ w, k + 1 < p * q) ∧
      real [univ] (.split 0 q :: layer 0 q p ++ swaps 0 w) = real [univ] (.split 0 p :: layer 0 p q)
  then Classical.choose h else []

theorem crtWord_lt (p q : ℕ) : ∀ k ∈ crtWord p q, k + 1 < p * q := by
  unfold crtWord
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · simp

/-- Instances of the relation families (a)–(d) of Fact O. -/
inductive Inst
  | sq (n k : ℕ)
  | br (n k : ℕ)
  | fsw (n k l : ℕ)
  | fsp (n i j p q : ℕ)
  | dl (n k i p : ℕ)
  | dr (n k i p : ℕ)
  | dk (n k p : ℕ)
  | dk1 (n k p : ℕ)
  | cx (n i p q : ℕ)

/-- The level of an instance. -/
def Inst.lev : Inst → ℕ
  | .sq n _ | .br n _ | .fsw n _ _ | .fsp n _ _ _ _ | .dl n _ _ _ | .dr n _ _ _ | .dk n _ _
  | .dk1 n _ _ | .cx n _ _ _ => n

/-- The two sides of an instance. -/
noncomputable def Inst.sides : Inst → List Move × List Move
  | .sq _ k => ([.swap k, .swap k], [])
  | .br _ k => ([.swap k, .swap (k + 1), .swap k], [.swap (k + 1), .swap k, .swap (k + 1)])
  | .fsw _ k l => ([.swap k, .swap l], [.swap l, .swap k])
  | .fsp _ i j p q => ([.split i p, .split (j + p - 1) q], [.split j q, .split i p])
  | .dl _ k i p => ([.swap k, .split i p], [.split i p, .swap (k + p - 1)])
  | .dr _ k i p => ([.swap k, .split i p], [.split i p, .swap k])
  | .dk _ k p => ([.swap k, .split k p], .split (k + 1) p :: swaps k (List.range p))
  | .dk1 _ k p => ([.swap k, .split (k + 1) p], .split k p :: swaps k (List.range p).reverse)
  | .cx _ i p q => (.split i p :: layer i p q, .split i q :: layer i q p ++ swaps i (crtWord p q))

/-- The relator of an instance. -/
noncomputable def Inst.rel (P : Set ℕ) (x : Inst) : FreeGroup (Gen P) :=
  toFree P x.lev x.sides.1 * (toFree P x.lev x.sides.2)⁻¹

/-- A numerical code of an instance. -/
def Inst.code : Inst → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  | .sq n k => (0, n, k, 0, 0, 0)
  | .br n k => (1, n, k, 0, 0, 0)
  | .fsw n k l => (2, n, k, l, 0, 0)
  | .fsp n i j p q => (3, n, i, j, p, q)
  | .dl n k i p => (4, n, k, i, p, 0)
  | .dr n k i p => (5, n, k, i, p, 0)
  | .dk n k p => (6, n, k, p, 0, 0)
  | .dk1 n k p => (7, n, k, p, 0, 0)
  | .cx n i p q => (8, n, i, p, q, 0)

theorem Inst.code_injective : Function.Injective Inst.code := by
  intro x y h
  cases x <;> cases y <;> simp_all [Inst.code]

/-- All numerical parameters of an instance are below `N`. -/
def Inst.Bound (N : ℕ) (x : Inst) : Prop :=
  x.code.1 < N + 9 ∧ x.code.2.1 < N + 9 ∧ x.code.2.2.1 < N + 9 ∧ x.code.2.2.2.1 < N + 9 ∧
    x.code.2.2.2.2.1 < N + 9 ∧ x.code.2.2.2.2.2 < N + 9

theorem bound_finite (N : ℕ) : {x : Inst | x.Bound N}.Finite := by
  have hI : (Set.Iio (N + 9)).Finite := Set.finite_Iio _
  have hS := hI.prod (hI.prod (hI.prod (hI.prod (hI.prod hI))))
  refine (hS.preimage Inst.code_injective.injOn).subset fun x hx => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The relators: bounded instances satisfying `valid`. -/
def relSet (P : Set ℕ) (N : ℕ) (valid : Inst → Prop) : Set (FreeGroup (Gen P)) :=
  {r | ∃ x : Inst, x.Bound N ∧ valid x ∧ r = x.rel P}

theorem relSet_finite (N : ℕ) (valid : Inst → Prop) : (relSet P N valid).Finite := by
  refine ((bound_finite N).image (Inst.rel P)).subset ?_
  rintro r ⟨x, hx, -, rfl⟩
  exact ⟨x, hx, rfl⟩

end GroupApproximation.ClassTransposition.Presentation
