# Pentagon RSG: the three finite checks (bh-finf-hyp, 2026-09-19)

## The runs

- Four short runs of `checks.py` on acn112, through the msi wrapper, as
  `taskset -c 30,31 nice -n 19 timeout 900`. Each took about 32 s, with `rc=0`.
- The final version is below, and its output is `checks4.out` in `/projects/standard/hsiehph/sauer354/bh-finf-hyp/`.
- Nothing ran locally.
- **Atoms.** Exact atoms of `B_n`, `n ≤ 6`, read on the sphere of radius 8.
- **True types.** BBMZ morphism types. They are found by testing every candidate `g = y x_0^{-1}` against
  condition (ii) (level shift) and condition (iii) (children map bijectively to children), on samples inside
  the ball.
  - Every morphism is among the candidates, so there are no false negatives. False positives would only merge
    types.

## Results

1. **Morphisms: no nontrivial self-morphisms.** There are 15 true types on levels 1–4, plus the root. The
   counts per level are 10, 15, 15, 15, and the relations close.
   - No type admits a nontrivial self-morphism, so every `Mor(v)` is trivial at the tested depth.
   - So a morphism between two atoms is unique, and it is the canonical similarity.
2. **Boundedness (check i): supported, with a paper argument.** For a reflection `s`, `d(s,·) − d(1,·) = ±1` is
   **exactly constant** on each half-space of its wall `H_s`, since `|sx| = |x| ± 1` according to the side.
   - Take `ξ ∈ ∂P` not an endpoint of `H_s`. It has a neighbourhood inside one half-space. There
     `B_n(s) ∩ H^± = B_(n∓1)(1) ∩ H^±`, so the fronts of deep atoms agree. As in
     `hyperbolic-cone-matching-holds-off-the-branch-locus`, `s` maps deep atoms onto atoms by morphisms, which
     are canonical by item 1.
   - So `sing(s)` lies in the fibres of `∂_h P → ∂P` over the two endpoints of `H_s`, which are finite
     (Webster–Winchester). This matches the 4 non-branching chains seen at every tested level.
   - Since `sing(gh) ⊆ h^{-1}sing(g) ∪ sing(h)`, and full-closure elements are piecewise in `P`, **every
     element of `[[P | ∂_h P]]` has finitely many singular points**, given item 1 at all depths.
3. **The true defect group (check ii): FAILS as stated.**
   - For the true types, `H_0 = coker(I − A^T) ≅ Z^5`, with Smith diagonal eleven 1's and no torsion. The coarse
     `H_0 ≅ Z` of the earlier run is a quotient of it.
   - The defect vectors of all `g` with `|g| ≤ 3` at level-4 atoms span a subgroup of **rank 5**.
   - Each generator's nonzero singular classes are `±y_s`, and `y_0, …, y_4` are independent: one direction per
     wall orbit, the five generators being pairwise non-conjugate.
   - But some vectors have coefficients `±1/2` in the `y_s` basis, and 128 of 195 atoms carry several classes.
     So `⟨Δ⟩` is a rank-5 lattice containing `⊕ Z y_s` with finite index. The naive decoupling into a join of five
     rank-1 complexes is **not** established.
4. **Interval defect sets (check iii):** moot in the rank-1 sense. In the `y_s` basis the nonzero coefficient
   values seen are `{±1/2, ±1}`.

## Consequence

The `F_∞` Theorem of `level-set-join-complexes-are-highly-connected` (defect group `Z`) does not apply to the
pentagon RSG. The surface-group corollary is **not** obtained. Two ways remain.
- **(a) A `Z^r` version of Theorem L.** Level sets of vector sums of finite sets containing 0 should still have
  linearly growing connectivity. The rank-1 proof uses that completion sums form intervals. In `Z^r`, sumsets of
  many copies fill the lattice points of a polytope away from its boundary (Khovanskii-type saturation), which is
  the natural substitute.
- **(b) Reduce the rank by enlarging the base.** Pass to the full closure of `P` together with the Thompson group
  of the coarse (shape) coding, whose `H_0` is `Z`, if that group is still a bounded full contracting RSG.
  - Its defects would then lie in `Z`, as `±x`, which are intervals.
  - This needs a rigid structure on the coarse type tree compatible with the true morphisms.

## Lesson for general BH

Defect groups see the full symmetry type of the coding. For the pentagon each wall orbit contributes its own
integer flux, so `⟨Δ⟩` has rank 5, the number of conjugacy classes of reflections, and not 1. A finiteness theorem
for surface-type hosts therefore needs either vector-valued level-set connectivity, or a coarser base that merges
the flux directions.

## Output of the final run

```
   25.4s ball=143281 fullkeys=143280
   28.1s A: true types on levels 1..4: 15; per level [10, 15, 15, 15]; types with a nontrivial self-morphism: []
   28.1s B: relations for 16 of 16 types (closed=True); Smith diagonal [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]; H_0 = Z^5 + torsion []
   31.3s C: 51 distinct defect vectors; rank of relations 11; rank with defects 16; rank <Delta> = 5
   31.3s C: defect values in <Delta> = Z (if rank 1): []; distinct per-atom value sets: []
   31.4s D: generator 0: 2 of 9 vectors are nonzero classes; chosen x_s = (0, -1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
   31.4s D: generator 0: distinct defect vectors at its level-4 chain atoms: [(0, -1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0), (0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0), (0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0)]
   31.4s D: generator 1: 2 of 9 vectors are nonzero classes; chosen x_s = (0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
   31.4s D: generator 1: distinct defect vectors at its level-4 chain atoms: [(0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0), (0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0), (0, 0, 0, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0)]
   31.4s D: generator 2: 2 of 9 vectors are nonzero classes; chosen x_s = (0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0)
   31.4s D: generator 2: distinct defect vectors at its level-4 chain atoms: [(0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0), (0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0), (0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0), (0, 1, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)]
   31.4s D: generator 3: 2 of 9 vectors are nonzero classes; chosen x_s = (0, 0, 0, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0)
   31.4s D: generator 3: distinct defect vectors at its level-4 chain atoms: [(0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0), (0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0), (0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1), (0, 0, 0, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0), (0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0)]
   31.4s D: generator 4: 2 of 9 vectors are nonzero classes; chosen x_s = (0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 0, 0, 0, 0)
   31.4s D: generator 4: distinct defect vectors at its level-4 chain atoms: [(0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0), (0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0), (0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0), (0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1), (0, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)]
   31.7s D: x_s independent mod relations: True; unsolved vectors: 0; support sizes {4: 2, 1: 20, 2: 10, 3: 9, 0: 10}; nonzero coefficient values [Fraction(-1, 1), Fraction(-1, 2), Fraction(1, 2), Fraction(1, 1)]; atoms whose vectors use >1 generator class: 128 of 195; coefficient values per class {3: [Fraction(-1, 1), Fraction(-1, 2), Fraction(1, 2), Fraction(1, 1)], 0: [Fraction(-1, 1), Fraction(-1, 2), Fraction(1, 2), Fraction(1, 1)], 4: [Fraction(-1, 1), Fraction(-1, 2), Fraction(1, 2), Fraction(1, 1)], 1: [Fraction(-1, 1), Fraction(1, 2), Fraction(1, 1)], 2: [Fraction(-1, 1), Fraction(-1, 2), Fraction(1, 2), Fraction(1, 1)]}
   31.7s ALL DONE
```

The script is in `gq-bh-finf-hyp-pentagon-three-checks-script.md`.
