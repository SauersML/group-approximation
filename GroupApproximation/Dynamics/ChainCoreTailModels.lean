import GroupApproximation.Meta.AxiomGuard

/-!
# Finite models of the printed identities of `prop:bilateral-three` and of the return tower

`non_mf_groups_exist.tex`, proof of Proposition `prop:bilateral-three` (tex lines 1549–1596), and the
tower paragraph of the proof of Corollary `cor:dynamic-rank-budget` (tex lines 1721–1733).

These are model tests, not carriers.  A crossed-product element acts on the finitely many points of one
cyclic orbit, and a `3 × 3` matrix over it is a sparse matrix over `ℤ/p` on three copies of that orbit.
A finite cycle cannot realize a proper compression `T(P) ⊊ P`, so nothing here proves the proposition;
the carriers belong to the builder lanes.  What the models settle is the arithmetic of the printed
displays: the level bookkeeping of `r` and `W`, and the sign of every commutator under the manuscript's
convention `[g,h] = g h g⁻¹ h⁻¹` (tex line 156).  Characteristic `2` cannot see signs, so the cell is also
checked at `p = 3`, with negative controls that fail at `p = 3` and are blind at `p = 2`.
-/

namespace GroupApproximation.ChainCoreTailModels

/-- A sparse square matrix over `ℤ/p`: `(row, column, coefficient)` triples; repeated positions add. -/
abbrev SpMat : Type := List (Nat × Nat × Nat)

/-- Entry `(i, j)` of a sparse matrix, reduced modulo `p`. -/
def spEntry (p : Nat) (A : SpMat) (i j : Nat) : Nat :=
  A.foldr (fun e acc => cond (Nat.beq e.1 i && Nat.beq e.2.1 j) (acc + e.2.2) acc) 0 % p

/-- The product of two sparse matrices over `ℤ/p`. -/
def spMul (p : Nat) (A B : SpMat) : SpMat :=
  A.foldr (fun a acc => B.foldr
    (fun b acc' => cond (Nat.beq a.2.1 b.1) ((a.1, b.2.1, a.2.2 * b.2.2 % p) :: acc') acc') acc) []

/-- The identity on the coordinates `0, …, n - 1`. -/
def spOne (n : Nat) : SpMat := (List.range n).map fun i => (i, i, 1)

/-- Whether two sparse matrices agree over `ℤ/p` on every entry `(i, j)` with `i, j < n`. -/
def spEqOn (p n : Nat) (A B : SpMat) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j => Nat.beq (spEntry p A i j) (spEntry p B i j)

/-- The transpose; it inverts a permutation matrix. -/
def spTranspose (A : SpMat) : SpMat := A.map fun e => (e.2.1, e.1, e.2.2)

/-- The commutator `[g, h] = g h g⁻¹ h⁻¹` of the manuscript (tex line 156), given the inverses. -/
def spComm (p : Nat) (g h gInv hInv : SpMat) : SpMat := spMul p (spMul p (spMul p g h) gInv) hInv

/-- The `k`-th power of a sparse `n × n` matrix over `ℤ/p`. -/
def spPow (p n : Nat) (A : SpMat) : Nat → SpMat
  | 0 => spOne n
  | k + 1 => spMul p (spPow p n A k) A

/-! ### The cell of `prop:bilateral-three` -/

/-- Levels of the cyclic orbit model: `0, 1` form `P`; `4, 3, 2` are the negative levels `-1, -2, -3`. -/
def period : Nat := 5

/-- Three matrix coordinates times the levels. -/
def dim : Nat := 3 * period

/-- The negative level `-j` as a residue modulo `period`. -/
def negLevel (j : Nat) : Nat := period - j

/-- The basis vector of matrix coordinate `c` (`0, 1, 2` for the printed `1, 2, 3`) at level `l`. -/
def pt (c l : Nat) : Nat := c * period + l

/-- `1 + v E_{(i,a),(j,b)}`, the root `e_{ij}(v f_{ab})` of the model. -/
def rootE (i a j b v : Nat) : SpMat := (pt i a, pt j b, v) :: spOne dim

/-- `diag(u, u, u)`: every coordinate moves one level up. -/
def shift : SpMat :=
  (List.range 3).foldr (fun c acc => (List.range period).foldr
    (fun l acc' => (pt c ((l + 1) % period), pt c l, 1) :: acc') acc) []

/-- `diag(1, 1, r)` with the printed `r = 1 - Σ_{j=1}^3 f_{-j,-j} + f_{-2,-1} + f_{-3,-2} + f_{-1,-3}`. -/
def rFormula (p : Nat) : SpMat :=
  (pt 2 (negLevel 1), pt 2 (negLevel 1), p - 1) :: (pt 2 (negLevel 2), pt 2 (negLevel 2), p - 1) ::
    (pt 2 (negLevel 3), pt 2 (negLevel 3), p - 1) :: (pt 2 (negLevel 2), pt 2 (negLevel 1), 1) ::
    (pt 2 (negLevel 3), pt 2 (negLevel 2), 1) :: (pt 2 (negLevel 1), pt 2 (negLevel 3), 1) :: spOne dim

/-- The cycle `-1 ↦ -2 ↦ -3 ↦ -1` on the third coordinate, by its action on points. -/
def cyc (x : Nat) : Nat :=
  cond (Nat.beq x (pt 2 (negLevel 1))) (pt 2 (negLevel 2)) <|
    cond (Nat.beq x (pt 2 (negLevel 2))) (pt 2 (negLevel 3)) <|
      cond (Nat.beq x (pt 2 (negLevel 3))) (pt 2 (negLevel 1)) x

/-- `diag(1, 1, r)` as the matrix of the permutation `cyc`. -/
def rAction : SpMat := (List.range dim).map fun x => (cyc x, x, 1)

/-- `W = diag(u, u, u) diag(1, 1, r)`. -/
def W (p : Nat) : SpMat := spMul p shift (rFormula p)

/-- The coefficient root `e_{ij}(Σ f_{ab})` over the listed level pairs `(a, b)`, all inside `P`. -/
def coeffRoot (i j : Nat) (levels : List (Nat × Nat)) : SpMat :=
  levels.map (fun q => (pt i q.1, pt j q.2, 1)) ++ spOne dim

/-- `ℓ = e_{21}(p)` with `p = 1_P`, `P = {0, 1}`. -/
def ell : SpMat := coeffRoot 1 0 [(0, 0), (1, 1)]

/-- The inverse `e_{21}(-p)` of `ℓ`. -/
def ellInv (p : Nat) : SpMat := [(pt 1 0, pt 0 0, p - 1), (pt 1 1, pt 0 1, p - 1)] ++ spOne dim

/-- The printed identities of the cell (tex 1560–1593) in the cyclic model over `ℤ/p`. -/
def bilateralCellCheck (p : Nat) : Bool :=
  let Wp := W p
  let Wi := spTranspose Wp
  let c := rootE 0 (negLevel 1) 2 (negLevel 2) 1
  let ci := rootE 0 (negLevel 1) 2 (negLevel 2) (p - 1)
  let y := rootE 2 (negLevel 1) 1 0 1
  let yi := rootE 2 (negLevel 1) 1 0 (p - 1)
  let z := rootE 2 (negLevel 1) 2 (negLevel 2) 1
  let zi := rootE 2 (negLevel 1) 2 (negLevel 2) (p - 1)
  let conj := spMul p (spMul p Wp c) Wi
  let conji := spMul p (spMul p Wp ci) Wi
  let dlt := spComm p conj ell conji (ellInv p)
  let dlti := rootE 1 0 2 (negLevel 2) 1
  let x := rootE 2 (negLevel 1) 0 0 1
  let xi := rootE 2 (negLevel 1) 0 0 (p - 1)
  -- the printed formula for `r` is the cycle, and `W` is invertible with inverse its transpose
  spEqOn p dim (rFormula p) rAction &&
  spEqOn p dim (spMul p Wp Wi) (spOne dim) && spEqOn p dim (spMul p Wi Wp) (spOne dim) &&
  -- `W c W⁻¹ = e_{13}(f_{0,-2})`
  spEqOn p dim conj (rootE 0 0 2 (negLevel 2) 1) &&
  -- `δ = [W c W⁻¹, ℓ] = e_{23}(-f_{0,-2})`, inverted by `e_{23}(f_{0,-2})`
  spEqOn p dim dlt (rootE 1 0 2 (negLevel 2) (p - 1)) && spEqOn p dim (spMul p dlt dlti) (spOne dim) &&
  -- `[y, δ] = z⁻¹`
  spEqOn p dim (spComm p y dlt yi dlti) zi &&
  -- `z` commutes with `W`, `c` and `y`, is not `1`, and `z^p = 1`
  spEqOn p dim (spMul p (spMul p Wp z) Wi) z && spEqOn p dim (spMul p z c) (spMul p c z) &&
  spEqOn p dim (spMul p z y) (spMul p y z) &&
  !spEqOn p dim z (spOne dim) && spEqOn p dim (spPow p dim z p) (spOne dim) &&
  -- `[z, e_{31}(f_{-2,0})] = e_{31}(f_{-1,0})`
  spEqOn p dim (spComm p z (rootE 2 (negLevel 2) 0 0 1) zi (rootE 2 (negLevel 2) 0 0 (p - 1))) x &&
  -- `[e_{23}(f_{0,-1}), e_{31}(f_{-1,0})] = e_{21}(d)`, with `d = f_{00}`
  spEqOn p dim (spComm p (rootE 1 0 2 (negLevel 1) 1) x (rootE 1 0 2 (negLevel 1) (p - 1)) xi)
    (rootE 1 0 0 0 1)

/-- Off-diagonal coefficient roots of `L` supported on `P × P`: constant, forward and backward levels. -/
def cellRoots : List SpMat :=
  [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)].foldr (fun ij acc =>
    coeffRoot ij.1 ij.2 [(0, 0), (1, 1)] :: coeffRoot ij.1 ij.2 [(1, 0)] ::
      coeffRoot ij.1 ij.2 [(0, 1)] :: acc) []

/-- `c`, `z` and `diag(1, 1, r)` centralize the coefficient roots (tex 1566, 1577, 1583), and `W` moves a
level-zero root coefficient to level one, `a ↦ u a u⁻¹` (tex 1567–1568). -/
def centralizerCheck (p : Nat) : Bool :=
  let c := rootE 0 (negLevel 1) 2 (negLevel 2) 1
  let z := rootE 2 (negLevel 1) 2 (negLevel 2) 1
  (cellRoots.all fun g =>
    spEqOn p dim (spMul p c g) (spMul p g c) && spEqOn p dim (spMul p z g) (spMul p g z) &&
      spEqOn p dim (spMul p (rFormula p) g) (spMul p g (rFormula p))) &&
  ([(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)].all fun ij =>
    spEqOn p dim (spMul p (spMul p (W p) (coeffRoot ij.1 ij.2 [(0, 0)])) (spTranspose (W p)))
      (coeffRoot ij.1 ij.2 [(1, 1)]))

/-- Negative controls: the other sign of `[y, δ]` and of `δ`, the unshifted level of `W c W⁻¹`, and `W`
without its correction `r` must all fail. -/
def bilateralSignControls (p : Nat) : Bool :=
  let Wp := W p
  let Wi := spTranspose Wp
  let c := rootE 0 (negLevel 1) 2 (negLevel 2) 1
  let ci := rootE 0 (negLevel 1) 2 (negLevel 2) (p - 1)
  let y := rootE 2 (negLevel 1) 1 0 1
  let yi := rootE 2 (negLevel 1) 1 0 (p - 1)
  let z := rootE 2 (negLevel 1) 2 (negLevel 2) 1
  let conj := spMul p (spMul p Wp c) Wi
  let conji := spMul p (spMul p Wp ci) Wi
  let dlt := spComm p conj ell conji (ellInv p)
  let dlti := rootE 1 0 2 (negLevel 2) 1
  !spEqOn p dim (spComm p y dlt yi dlti) z && !spEqOn p dim dlt (rootE 1 0 2 (negLevel 2) 1) &&
    !spEqOn p dim conj c && !spEqOn p dim (spMul p (spMul p shift z) (spTranspose shift)) z

theorem bilateralCell_mod_two : bilateralCellCheck 2 = true := by decide +kernel

theorem bilateralCell_mod_three : bilateralCellCheck 3 = true := by decide +kernel

theorem bilateralCentralizer_mod_two : centralizerCheck 2 = true := by decide +kernel

theorem bilateralSignControls_mod_three : bilateralSignControls 3 = true := by decide +kernel

/-- Calibration: characteristic `2` cannot tell the printed signs from their negatives. -/
theorem bilateralSignControls_mod_two_blind : bilateralSignControls 2 = false := by decide +kernel

/-! ### The return tower of `cor:dynamic-rank-budget` -/

/-- `a_i = u^i 1_{D_i}` on the cyclic system `ℤ/N`. -/
def towerA (N i : Nat) (D : List Nat) : SpMat := D.map fun x => ((x + i) % N, x, 1)

/-- `b_i = 1_{D_i} u^{-i}` on the cyclic system `ℤ/N`. -/
def towerB (N i : Nat) (D : List Nat) : SpMat := D.map fun x => (x, (x + i) % N, 1)

/-- The indicator `1_D`. -/
def indicator (D : List Nat) : SpMat := D.map fun x => (x, x, 1)

/-- The printed tower identities (tex 1731–1732) for the cuts `(i, D_i)`, over `ℤ/p`:
`b_i a_j = 0` for `i ≠ j`, `b_i a_i = 1_{D_i}`, and `Σ_i a_i b_i = 1`. -/
def towerCheck (p N : Nat) (cuts : List (Nat × List Nat)) : Bool :=
  (cuts.all fun ci => cuts.all fun cj =>
    spEqOn p N (spMul p (towerB N ci.1 ci.2) (towerA N cj.1 cj.2))
      (cond (Nat.beq ci.1 cj.1) (indicator ci.2) [])) &&
  spEqOn p N (cuts.foldr (fun ci acc => spMul p (towerA N ci.1 ci.2) (towerB N ci.1 ci.2) ++ acc) [])
    (spOne N)

/-- On `ℤ/N`: `C` is separated from its first `r - 1` translates, `X = ⋃_{|j|<r} T^j C`, and every
return gap of `C` lies in `[r, 2r - 1]` (tex 1716–1718). -/
def sectionCheck (N r : Nat) (C : List Nat) : Bool :=
  let inC := fun x => C.any fun c => Nat.beq c x
  ((List.range r).all fun j => Nat.beq j 0 || C.all fun c => !inC ((c + j) % N)) &&
  ((List.range N).all fun x => (List.range r).any fun j => inC ((x + j) % N) || inC ((x + N - j) % N)) &&
  (C.all fun c => (List.range (2 * r)).any fun h => Nat.ble r h && inC ((c + h) % N) &&
    (List.range h).all fun g => Nat.beq g 0 || !inC ((c + g) % N))

/-- The matrix-group case `r = 2` on `ℤ/7` with `C = {0, 2, 4}`: return times `2, 2, 3`, so
`D_0 = D_1 = C` and `D_2 = {4}`. -/
theorem returnTower_matrixGroups :
    sectionCheck 7 2 [0, 2, 4] = true ∧
      towerCheck 2 7 [(0, [0, 2, 4]), (1, [0, 2, 4]), (2, [4])] = true := by
  decide +kernel

/-- The unit-group case `r = 3` on `ℤ/8` with `C = {0, 3}`: return times `3, 5`, so
`D_0 = D_1 = D_2 = C` and `D_3 = D_4 = {3}`. -/
theorem returnTower_unitGroup :
    sectionCheck 8 3 [0, 3] = true ∧
      towerCheck 2 8 [(0, [0, 3]), (1, [0, 3]), (2, [0, 3]), (3, [3]), (4, [3])] = true := by
  decide +kernel

/-- Negative control: cutting `D_2 = C` instead of the return-time cell breaks the tower identities. -/
theorem returnTower_wrongCut : towerCheck 2 7 [(0, [0, 2, 4]), (1, [0, 2, 4]), (2, [0, 2, 4])] = false := by
  decide +kernel

end GroupApproximation.ChainCoreTailModels

#audit_closed_axioms GroupApproximation.ChainCoreTailModels.bilateralCell_mod_two
#audit_closed_axioms GroupApproximation.ChainCoreTailModels.bilateralCell_mod_three
#audit_closed_axioms GroupApproximation.ChainCoreTailModels.bilateralCentralizer_mod_two
#audit_closed_axioms GroupApproximation.ChainCoreTailModels.bilateralSignControls_mod_three
#audit_closed_axioms GroupApproximation.ChainCoreTailModels.bilateralSignControls_mod_two_blind
#audit_closed_axioms GroupApproximation.ChainCoreTailModels.returnTower_matrixGroups
#audit_closed_axioms GroupApproximation.ChainCoreTailModels.returnTower_unitGroup
#audit_closed_axioms GroupApproximation.ChainCoreTailModels.returnTower_wrongCut
