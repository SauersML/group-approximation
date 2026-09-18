---
rg: 2
id: minimal-torsion-free-small-tree-lattices-not-lo-proof
kind: route
title: Four-vertex complete VH complexes of degree (3,3) and (3,4) enumerated exhaustively; reducible classes certified by finite automaton images, the rest refuted by positive-cone SAT
target: minimal-torsion-free-small-tree-lattices-not-left-orderable
requires: []
artifacts:
  - experiments/bmw-census-left-orders-2026-09-17/README.md
  - experiments/bmw-census-left-orders-2026-09-17/cx4.py
  - experiments/bmw-census-left-orders-2026-09-17/cxmn.py
  - experiments/bmw-census-left-orders-2026-09-17/crosscheck_cx.py
  - experiments/bmw-census-left-orders-2026-09-17/crosscheck_cx.log
  - experiments/bmw-census-left-orders-2026-09-17/summarize_cx.py
  - experiments/bmw-census-left-orders-2026-09-17/summarize_cx.log
  - experiments/bmw-census-left-orders-2026-09-17/cx4_parity.py
  - experiments/bmw-census-left-orders-2026-09-17/cxmn_parity.py
---

All scripts are in `experiments/bmw-census-left-orders-2026-09-17/`. Each step below is either
elementary or a finite computation done by a named script.

Degree (3,3) uses `cx4.py`. Degree (3,4) uses `cxmn.py`, which is the same code with general
`(m,n)`.

## 1. Reduction to four-vertex data

Let `Γ ≤ Aut(T_m) × Aut(T_n)` be a torsion-free type-preserving lattice with four vertex orbits.

**`Γ` acts freely on vertices.** A vertex stabilizer is compact open intersected with a discrete
group, so it is finite. Since `Γ` is torsion-free, it is trivial.

**`Γ` is free on all cells.** A group element mapping a cell to itself preserves types, so it fixes
a vertex of that cell and is trivial.

**The quotient.** Let `X = Γ \ (T_m × T_n)`. Label its vertices `(i,j)` by type.
- Every horizontal edge joins `(0,j)` to `(1,j)`, and every vertical edge joins `(i,0)` to `(i,1)`.
- The covering map is a local isomorphism, so every link is `K_{m,n}`.
- So each row `j` carries `m` horizontal edges `h_j ∈ {0..m-1}`, and each column `i` carries `n`
  vertical edges `v_i ∈ {0..n-1}`.
- Every square has four distinct corners, so it is a quadruple `(h0, v1, h1, v0)`.
- The link condition says that each of the pairs `(h0,v0)`, `(h0,v1)`, `(h1,v1)`, `(h1,v0)` lies in
  exactly one square.

**Converse.** Such a complex is a compact VH complex with links `K_{m,n}`. Its universal cover is
`T_m × T_n` (Burger–Mozes, Wise), and `π_1 X` acts freely, type-preservingly and with four vertex
orbits.

So `Γ ≅ π_1(X, (0,0))`.

**Encoding.**
- A datum is encoded by permutations `P[h0] : v0 ↦ v1` and `Q[v0] : h0 ↦ h1`. They are permutations
  because `(h0,v1)` and `(h1,v0)` occur exactly once.
- The remaining condition is that the `m·n` pairs `(v1,h1)` are distinct.

## 2. Enumeration and symmetries

**Normalization.**
- Relabelling the column-1 labels by `P[0]^{-1}` and the row-1 labels by `Q[0]^{-1}` gives a datum
  with `P[0] = id` and `Q[0] = id`.
- So every relabelling orbit meets the normalized set.
- `enumerate_normalized` backtracks over `Q[1..n-1]`, for every `P[1..m-1]`.

**Cross-check (`crosscheck_cx.py`).** The script compares the backtracker with a brute force over all
`P[1..m-1]` and `Q[1..n-1]`. The two produce the same sets: 244 data in degree (3,3) and 7584 in
degree (3,4). In degree (3,3), `cx4.py` independently brute-forces all `P, Q` without
normalizing. It gets `8784 = 244 · 3! · 3!` data and asserts that the orbit sizes sum to 8784.

**Symmetries.** Classes are taken up to the following moves:
- *Row swap* `(h0,v1,h1,v0) ↦ (h1,v1,h0,v0)`. This is the same complex with the types `j` renamed,
  so `π_1` is based at another vertex and the lattice is the same.
- *Column swap* `(h0,v1,h1,v0) ↦ (h0,v0,h1,v1)`. The same, for the types `i`.
- *Independent relabellings* of the four label sets. This gives an isomorphic complex.
- *Transpose* `(h0,v1,h1,v0) ↦ (v0,h1,v1,h0)`, when `m = n`. This exchanges the two factors.

None of these moves changes the isomorphism type of `Γ`, whether it is irreducible, or whether it
is left-orderable. `crosscheck_cx.py` checks that the class orbits partition the normalized data:
the sizes of their normalized parts sum to the total, and their union is everything. This gives
11 classes in degree (3,3), agreeing with `cx4.py`, and 98 classes in degree (3,4).

## 3. Normal forms and multiplication

**Normal forms.**
- In `T_m × T_n` any two vertices are joined by a unique path consisting of a reduced vertical
  path followed by a reduced horizontal path.
- An edge path from `(0,0)` in `X` is determined by its label sequence, because of the covering.
- So `Γ` is in bijection with the pairs `(V, H)` where:
  - `V` is a reduced word in `{0..n-1}`, read in column 0;
  - `H` is a reduced word in `{0..m-1}`, read in row `|V| mod 2`;
  - both have even length, since the endpoint has type `(0,0)`.

**Corner table.** `CX.T[(r, c, h_r, v_c)] = (v_{1-c}, h_{1-r})` for every square. It records the
homotopy across that square: the path "horizontal `h_r` in row `r` ending in column `c`, then
vertical `v_c`" is homotopic to "vertical `v_{1-c}` in column `1-c`, then horizontal `h_{1-r}` in
row `1-r`". Both paths run from `(1-c, r)` to `(c, 1-r)`.

**`CX.mul(g1, g2)`.**
- For each vertical letter of `g2`, it pushes the letter leftward through the current horizontal
  word using the corner table. The row index `r` stays fixed and the column index alternates.
- It then appends the letter to `V`, cancelling a backtrack.
- Finally it appends the horizontal letters of `g2`, cancelling backtracks.
- Each step is a homotopy rel endpoints, and the result has the normal form above. So `mul`
  computes the product in `Γ`.

**`inv` and checks.** `inv(V,H) = ((), H^rev) · (V^rev, ())`. `selfcheck` tests associativity and
`g g^{-1} = 1` on random triples from the ball of radius 4 (radius 6 in `cx4.py`) for every class.

## 4. Positive-cone SAT

This is the lemma of `small-degree-bmw-parity-kernels-not-left-orderable-proof` §4.

**Lemma.** If `Γ` is left-orderable, then for every finite `S ⊆ Γ \ {1}` closed under inverses the
indicator of the positive cone satisfies:
- `p_g ⊕ p_{g^{-1}}` for every `g ∈ S`;
- `¬p_g ∨ ¬p_h ∨ p_{gh}` whenever `g, h, gh ∈ S`;
- `¬p_g ∨ ¬p_h` whenever `gh = 1`.

**Instance.** `lo_sat(G, R, short)` takes `S` to be the normal forms with `|V| + |H| ≤ R`. It uses
either all products, or only those with one factor of length at most `short`. `solve` requires
CaDiCaL 1.5.3 and Glucose 4 to agree.

**Torsion-freeness.** `Γ` is torsion-free, and `lo_sat` asserts `g^{-1} ≠ g` for every `g`.

## 5. Finite images imply reducibility

**The two loop groups.**
- Let `Γ_h = {((), H)}`, the stabilizer in `Γ` of the base vertex `y_0` of `T_n`.
- Let `Γ_v = {(V, ())}`, the stabilizer of `x_0 ∈ T_m`.
- `Γ` acts simply transitively on the vertices of type `(0,0)`. So `Γ_h` acts simply transitively
  on type-0 vertices of `T_m`, and `Γ_v` on type-0 vertices of `T_n`.

**What `finite_image(G)` computes.** It computes the image of `Γ_h` in `Aut(T_n, y_0)`.
- The action of a horizontal word on vertical paths is the Mealy transducer obtained by pushing
  vertical letters through it (§3).
- Its states are the letters `(r, c, e)`, and the transition is the corner table.
- `E_k` is the set of transducers given by arbitrary words of length `k` in row-0 letters. The
  column is forced by `k`.

**How it decides equality.**
- The script builds the transducer of each word of length `k+1` as "last letter composed with a
  state of `E_k`".
- It Moore-minimizes everything built so far.
- States in one class have equal outputs and successors in equal classes. By induction on depth
  they define the same tree map.
- So the equality `levels[k] = levels[k-2]` of class sets gives `E_k = E_{k-2}` as sets of maps.

**Why stabilization gives finiteness.**
- `E_k ⊆ E_{k+2}`, because `e e` is a backtrack.
- `E_{k+1}` is `E_k` composed with the letters of column `(k+1) mod 2`, the same letter set as for
  `E_{k-1}`.
- So `E_k = E_{k-2}` implies `E_{k+1} = E_{k-1}`, and by induction the sequence is 2-periodic from
  `k-2` on.
- The image of `Γ_h` is the union of `E_j` over even `j`, which is `E_k` or `E_{k-1}`. This is
  finite, and the script returns `|E_k ∪ E_{k-1}|`.
- If minimization exceeds 4000 classes, the script returns `None` instead.

`finite_image(G, True)` runs the same computation on the transposed complex, giving the image of
`Γ_v` in `Aut(T_m, x_0)`.

**Lemma.** If both images are finite, `Γ` is reducible.

*Proof.* Let `N_h = ker(Γ_h → Aut T_n)` and `N_v = ker(Γ_v → Aut T_m)`. Both have finite index.
- Elements of `N_h` act as `(α, id)`, and elements of `N_v` act as `(id, β)`. So the two groups
  commute elementwise. They intersect trivially, since `Γ` acts freely.
- `N_h` has finitely many orbits on type-0 vertices of `T_m`, because `Γ_h` is simply transitive
  there. Likewise `N_v` has finitely many orbits on type-0 vertices of `T_n`.
- `H = N_h × N_v` acts coordinatewise. So its orbits on the type-`(0,0)` vertices are products of
  orbits, and there are finitely many.
- `Γ` is simply transitive on those vertices, so `[Γ : H]` equals the number of `H`-orbits, which
  is finite.

Take `Λ_1 = N_h` and `Λ_2 = N_v`. ∎

## 6. Outcome and assembly

**Runs.**
- `python3 cx4.py run census_cx4_33.json 0 11` writes `out_cx4_33.jsonl`.
- `python3 cxmn.py run 3 4 0 98` writes `out_cx_34.jsonl`. It was run in chunks, and
  `err_cx_34.log` is empty.

**Per-class plan.** Each class records `finH` and `finV`, then runs the positive-cone instance at
radius 4 with all products. If an image is not certified finite, it continues with:
- radius 6 with one factor of length at most 4;
- radius 6 with all products;
- radius 8 with one factor of length at most 2.

It stops at the first UNSAT.

**Tally (`summarize_cx.py`).** The script asserts that every class that is not certified reducible
stops UNSAT. In every such class both images are uncertified.

| degree | reducible | candidates | UNSAT at R4 | UNSAT at R6, short 4 | UNSAT at R8, short 2 |
|---|---|---|---|---|---|
| (3,3) | 9 | 2 | 1 | 1 | 0 |
| (3,4) | 64 | 34 | 13 | 20 | 1 (class 72) |

The maximum certified image order is 108.

**Proof of the theorem.** Let `Γ` be irreducible, torsion-free, type-preserving and with four vertex
orbits, of degree (3,3) or (3,4).
- By §1 and §2, `Γ` is isomorphic to `π_1` of a representative of some class.
- By §5 that class is not certified reducible.
- By the tally, the class has an UNSAT positive-cone instance. So by §4, `Γ` is not
  left-orderable. ∎

## 7. Consistency checks

**Parity maps.**
- The parity kernel of the BMW datum `SQ` is `π_1` of the four-vertex complex
  `{(h, v, h', v') : SQ(h,v) = (v',h')}`.
- `cx4_parity.py` maps all 60 BMW classes of degree (3,3) into the (3,3) census.
- `cxmn_parity.py` maps all 639 BMW classes of degree (4,3) into the (3,4) census, after transposing.
- In every case the reducible verdict of the one-vertex computation (`lo_census.finite_image`)
  agrees with the four-vertex computation above. These are two different automata on two different
  complexes.

**Calibration.**
- Radu's `Γ_R` (BMW class `30_30#10`) lands in class 6. That class is SAT at radius 4 and UNSAT at
  radius 6 with short factors of length 4, exactly as in the BMW census.
- The commuting product datum is class 0, with images of order 1 and a SAT radius-4 instance.
