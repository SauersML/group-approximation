import GroupApproximation.Meta.AxiomGuard

/-!
# Finite models of the two-ended example: the codimension count and the no-wraparound window

`non_mf_groups_exist.tex`, the remark after Corollary `cor:dynamic-rank-budget` (tex 1781–1791). The ring
`R_X` of the shift on `X = ℤ ∪ {−∞, +∞}`, endpoints fixed, over `𝔽₂`, acts faithfully on `𝔽₂^{(ℤ)}`:

> A unit has Laurent symbols $z^{a_-},z^{a_+}$ at the two ends and acts by these translations on
> the two sufficiently distant tails.  The tails starting at $-N$ and $N$ span a subspace of
> codimension $2N-1$, whose image has codimension $2N-1+a_+-a_-$.  Invertibility forces $a_+=a_-$;
> removing that common shift leaves a finite invertible block extended by identity.
> This semidirect product is LEF: copy any finite table's finitary supports and the translated
> supports used in its products into a sufficiently long finite cycle, replacing the shift by cyclic
> translation.  Products agree without wraparound; equal shift exponents are separated by their
> finitary parts, and different exponents by points outside those supports.

These are model tests, not carriers.  The carriers belong to the lane that owns the two-ended example.
No census row names them.

* **Codimension count.** A window of integers is counted directly: the basis indices outside the tails,
  and those outside the translated tails, for `N ∈ {3, 4, 5}` and symbols `|a₋|, |a₊| ≤ 2`, so the two
  image tails are disjoint. The printed orientation `a₊ - a₋` is checked, together with a negative control
  where the reversed orientation fails.
* **Calibration.** The explicit operators over `𝔽₂` are the defect pair `s = u p + 1 - p` and
  `t = p u⁻¹ + 1 - p` with symbols `(0, 1)` and `(0, -1)`, the shift `u`, and the block `e₁ ↦ e₁ + e₀`.
  Checked: `t s = 1`, `s t = 1 - 1_{0}`, `s` misses exactly `e₀`, and `u⁻¹ (u g) = g` for the block `g`,
  a finite invertible block extended by identity.
* **No-wraparound window.** Elements of `GL_fin ⋊ ℤ` are modelled as a nonnegative exponent `a` and a word
  of transvections, acting by `v ↦ g (σ^a v)`. The copy in the cycle `ℤ/M` reduces supports modulo `M` and
  turns the shift into cyclic translation.
  - On the table (the shift, two transvections sharing a coordinate pair, a disjoint one, and all pairwise
    products), equality in the cycle of length `11` is equality on the line.
  - Products agree there, and the separation claims hold.
  - In the cycle of length `3` the copy is not well defined (disjoint transvections stop commuting).
-/

namespace GroupApproximation.TwoEndedTailModels

/-! ### The codimension count (tex 1782–1784) -/

/-- The integers `-L, …, L`. -/
def window (L : Nat) : List Int := (List.range (2 * L + 1)).map fun t : Nat => (t : Int) - (L : Int)

/-- The window indices outside the span of the tails `i ≤ -N` and `i ≥ N`. -/
def tailComplement (N : Int) (L : Nat) : Nat := (window L).countP fun i => decide (-N < i ∧ i < N)

/-- The window indices outside the image of the tails, when the left tail is translated by `am` and the right
tail by `ap`. An index `i` is a left image iff `i - am ≤ -N`, and a right image iff `i - ap ≥ N`. -/
def imageComplement (N am ap : Int) (L : Nat) : Nat :=
  (window L).countP fun i => decide (-N < i - am ∧ i - ap < N)

/-- The symbols tested. -/
def symbols : List Int := [-2, -1, 0, 1, 2]

/-- The printed counts: `2N - 1` for the tails and `2N - 1 + a₊ - a₋` for their image. -/
def codimensionCheck : Bool :=
  ([3, 4, 5] : List Int).all fun N => decide ((tailComplement N 12 : Int) = 2 * N - 1) &&
    symbols.all fun am => symbols.all fun ap =>
      decide ((imageComplement N am ap 12 : Int) = 2 * N - 1 + ap - am)

/-- Negative control: the reversed orientation `2N - 1 + a₋ - a₊` fails. -/
def reversedCodimensionFails : Bool :=
  !(symbols.all fun am => symbols.all fun ap =>
      decide ((imageComplement 3 am ap 12 : Int) = 2 * 3 - 1 + am - ap))

/-! ### Calibration on explicit operators over `𝔽₂` -/

/-- A sparse vector of `𝔽₂^{(ℤ)}`: a list of basis indices, counted modulo `2`. -/
abbrev Vec : Type := List Int

/-- The odd-multiplicity indices of a vector. -/
def reduce (v : Vec) : List Int := v.eraseDups.filter fun i => v.count i % 2 == 1

/-- Whether two vectors agree over `𝔽₂`. -/
def sameVec (v w : Vec) : Bool :=
  (reduce v).all (fun i => (reduce w).contains i) && (reduce w).all (fun i => (reduce v).contains i)

/-- The linear extension of an operator given on basis vectors. -/
def extend (f : Int → Vec) (v : Vec) : Vec := v.flatMap f

/-- `s = u p + 1 - p`, `P = {0, 1, …} ∪ {+∞}`: symbols `(a₋, a₊) = (0, 1)`. -/
def sOp (i : Int) : Vec := if 0 ≤ i then [i + 1] else [i]

/-- `t = p u⁻¹ + 1 - p`: symbols `(0, -1)`. -/
def tOp (i : Int) : Vec := if 1 ≤ i then [i - 1] else if i = 0 then [] else [i]

/-- The bilateral shift `u`: symbols `(1, 1)`. -/
def uOp (i : Int) : Vec := [i + 1]

/-- The inverse shift `u⁻¹`: symbols `(-1, -1)`. -/
def uInvOp (i : Int) : Vec := [i - 1]

/-- The transvection `e₁ ↦ e₁ + e₀`: symbols `(0, 0)`. -/
def blockOp (i : Int) : Vec := if i = 1 then [1, 0] else [i]

/-- The window indices hit by no image `f e_j`, `j ∈ [-L - 3, L + 3]`, for a monomial operator `f`. -/
def missed (f : Int → Vec) (L : Nat) : List Int :=
  (window L).filter fun i => !((window (L + 3)).any fun j => (reduce (f j)).contains i)

/-- The printed calibration, on the window `[-6, 6]`. -/
def operatorCheck : Bool :=
  (window 6).all (fun i => sameVec (extend tOp (sOp i)) [i]) &&
  (window 6).all (fun i => sameVec (extend sOp (tOp i)) (if i = 0 then [] else [i])) &&
  decide (missed sOp 6 = [0]) && decide (missed uOp 6 = []) && decide (missed tOp 6 = []) &&
  (window 6).all (fun i => sameVec (extend uInvOp (uOp i)) [i] && sameVec (extend uOp (uInvOp i)) [i]) &&
  (window 6).all (fun i => sameVec (extend blockOp (blockOp i)) [i]) &&
  (window 6).all (fun i => sameVec (extend uInvOp (extend uOp (blockOp i))) (blockOp i)) &&
  (window 6).all (fun i => decide (i = 1) || sameVec (blockOp i) [i])

/-! ### The no-wraparound window (tex 1786–1791) -/

/-- A transvection `τ(i, j) : e_j ↦ e_j + e_i`. -/
abbrev Tr : Type := Nat × Nat

/-- Apply a transvection to a sparse vector, basis indices counted modulo `2`. -/
def applyTr (τ : Tr) (v : List Nat) : List Nat :=
  v.foldr (fun x acc => if x = τ.2 then x :: τ.1 :: acc else x :: acc) []

/-- An element `(a, g)` of `GL_fin ⋊ ℤ`, `a ≥ 0` and `g` a word of transvections, acting by `v ↦ g (σ^a v)`. -/
abbrev El : Type := Nat × List Tr

/-- The action on the line. -/
def actLine (x : El) (v : List Nat) : List Nat :=
  x.2.foldr applyTr (v.map fun i => i + x.1)

/-- The product `(a, g)(b, h) = (a + b, g · σ^a h σ^{-a})`. -/
def mulEl (x y : El) : El :=
  (x.1 + y.1, x.2 ++ y.2.map fun τ => (τ.1 + x.1, τ.2 + x.1))

/-- The copy in the cycle `ℤ/M`: supports reduced modulo `M`, the shift replaced by cyclic translation. -/
def actCycle (M : Nat) (x : El) (v : List Nat) : List Nat :=
  x.2.foldr (fun τ acc => applyTr (τ.1 % M, τ.2 % M) acc) (v.map fun i => (i + x.1) % M)

/-- The odd-multiplicity indices of a vector. -/
def reduceN (v : List Nat) : List Nat := v.eraseDups.filter fun i => v.count i % 2 == 1

/-- Whether two vectors agree over `𝔽₂`. -/
def sameVecN (v w : List Nat) : Bool :=
  (reduceN v).all (fun i => (reduceN w).contains i) && (reduceN w).all (fun i => (reduceN v).contains i)

/-- Equality on the line: equal exponents, and agreement on `e_0, …, e_{W-1}`, a range containing every
support used. Outside it both elements act as the same translation. -/
def eqLine (W : Nat) (x y : El) : Bool :=
  x.1 == y.1 && (List.range W).all fun i => sameVecN (actLine x [i]) (actLine y [i])

/-- Equality of the copies in the cycle `ℤ/M`. -/
def eqCycle (M : Nat) (x y : El) : Bool :=
  (List.range M).all fun i => sameVecN (actCycle M x [i]) (actCycle M y [i])

/-- The generators of the table: the shift, two transvections on one coordinate pair, and a transvection on
disjoint coordinates. -/
def gens : List El := [(1, []), (0, [(5, 6)]), (0, [(6, 5)]), (0, [(7, 8)])]

/-- The table: the generators and their pairwise products. Every support lies in `[5, 9]` and every exponent in
`[0, 2]`. So every changed column `j - a` is a nonnegative source, and columns `0, …, 11` see all of both
elements on the line `ℤ`. -/
def table : List El := gens ++ gens.flatMap fun x => gens.map fun y => mulEl x y

/-- The copy is well defined and injective on the table: equality in the cycle is equality on the line. -/
def windowCheck (M : Nat) : Bool :=
  table.all fun x => table.all fun y => eqLine 12 x y == eqCycle M x y

/-- The copy of a product is the product of the copies. -/
def productCheck (M : Nat) : Bool :=
  table.all fun x => gens.all fun y =>
    (List.range M).all fun i => sameVecN (actCycle M (mulEl x y) [i]) (actCycle M x (actCycle M y [i]))

/-- The coordinates a word touches. -/
def support (x : El) : List Nat := x.2.flatMap fun τ => [τ.1, τ.2]

/-- Whether the cycle coordinate `i` avoids both supports. -/
def outside (M : Nat) (x y : El) (i : Nat) : Bool := !((support x ++ support y).any fun j => j % M == i)

/-- The copies of different elements are separated by a point `i`. With equal exponents, `σ^a i` lies in
a support. With different exponents, `σ^a i` and `σ^b i` both lie outside the supports. -/
def separationCheck (M : Nat) : Bool :=
  table.all fun x => table.all fun y =>
    eqLine 12 x y ||
      (List.range M).any fun i =>
        !sameVecN (actCycle M x [i]) (actCycle M y [i]) &&
          if x.1 == y.1 then !outside M x y ((i + x.1) % M)
          else outside M x y ((i + x.1) % M) && outside M x y ((i + y.1) % M)

theorem codimension_count : codimensionCheck = true := by decide +kernel

theorem codimension_reversed_fails : reversedCodimensionFails = true := by decide +kernel

theorem operator_calibration : operatorCheck = true := by decide +kernel

theorem window_eleven : windowCheck 11 = true := by decide +kernel

theorem products_eleven : productCheck 11 = true := by decide +kernel

theorem separation_eleven : separationCheck 11 = true := by decide +kernel

/-- Negative control: in the cycle of length `3` the copy wraps around and is not well defined. -/
theorem window_three_wraps : windowCheck 3 = false := by decide +kernel

end GroupApproximation.TwoEndedTailModels

#audit_closed_axioms GroupApproximation.TwoEndedTailModels.codimension_count
#audit_closed_axioms GroupApproximation.TwoEndedTailModels.codimension_reversed_fails
#audit_closed_axioms GroupApproximation.TwoEndedTailModels.operator_calibration
#audit_closed_axioms GroupApproximation.TwoEndedTailModels.window_eleven
#audit_closed_axioms GroupApproximation.TwoEndedTailModels.products_eleven
#audit_closed_axioms GroupApproximation.TwoEndedTailModels.separation_eleven
#audit_closed_axioms GroupApproximation.TwoEndedTailModels.window_three_wraps
