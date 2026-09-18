# Bounded GAP/RCWA search for a finitely generated non-strongly shift-similar group (2026-09-18)

Lane bh-houghton-presentation, approved by the coordinator: 3 runs, single core, ≤ 10 min each, output on
`/projects/standard/hsiehph/sauer354/gqsrc/bh-houghton-presentation/`, and nothing left running. The software is
GAP 4.13.1 from the release tarball, built in user space there, with the bundled RCWA and ResClasses packages
(the IO package was compiled for the FR dependency).

**Target.** `fg-infinite-shift-similar-groups-are-strongly-shift-similar`. By
`shift-similar-germ-groups-are-ascending-hnn-extensions` item 4, a counterexample is a finitely generated
`Δ <= NearSym(N)` containing the shift whose index character is one-sided in `Σ^1`. Inside RCWA⁺(Z) (class-wise
order-preserving residue-class-wise affine permutations), germs at `+∞` are faithful and the index is the
`N_0`-index. So exact RCWA arithmetic decides equalities. Convention: `c(g) = nu*g*nu^-1` in GAP's right action,
with `nu = ClassShift(0,1)`, i.e. `n -> g(n+1) - 1`.

## Calibration (runs 1–2, identical output)
    cal: 3^tau = 6 (expect 6);  2^c(tau) = 5 (expect 5)          tau = ClassTransposition(1,2,2,4)
    cal: x_2 maps 3 to 8 (expect 2*3+2 = 8)                      x_k = c^k(tau): n <-> 2n+k
    cal: (x_0*x_2)^3 = 1 ? true ; x_0*x_2 = 1 ? false            (hand computation confirmed)
    cal: c(alpha) = alpha^-1 ? true                              alpha = ClassShift(1,2)*ClassShift(0,2)^-1
    cal: c(x_0) = x_1 ? true ; c^-1(x_1) = x_0 ? true
Run 1 stopped after calibration because `Search` is a read-only GAP name. Run 2 is the same script with the
function renamed.

## Run 2: forward and backward closure of shifted class transpositions
For seed `g` and `L`, put `B_L = < g, c(g), ..., c^L(g) >`. The run enumerated a word ball in `B_L`, with at
most 4000 new elements per level and modulus at most `2^10`. It tested `c^(L+1)(g) ∈ B_L` (forward closure,
giving `c(B_L) ⊆ B_L`) and `c^-1(g) ∈ B_L` (backward closure).

| seed | L = 1 (ball) | L = 2 (ball) | L = 3 (ball) | forward / backward found |
|---|---|---|---|---|
| CT(1,2,2,4) | 19 | 4905 | 9272 | no / no |
| CT(0,2,1,4) | 19 | 4905 | 9272 | no / no |
| CT(1,2,0,4) | 19 | 4905 | 9272 | no / no |
| CT(0,2,3,4) | 19 | 4905 | 9272 | no / no |
| CT(1,3,0,6) | 12 | 5032 | 8138 | no / no |
| CT(0,3,1,6) | 12 | 5032 | 8138 | no / no |

Total time 398 s. These `c`-orbits did not close up within the balls.

## Run 3: Thompson-F prototype search
Candidates:
- the 14 class transpositions of `ClassPairs(4)`, the 14 slides `ClassShift(r1,m1)*ClassShift(r2,m2)^-1` and their
  inverses (42 in all);
- all products of two of those;
- all products of three class transpositions from `ClassPairs(3)`.

That is 1870 elements, all of index 0. Tests on each `y`:
- relA: `c(y) = y^-1` (planted positive);
- relP: `c(y) = y^(±2)` (the lemma `no-nontrivial-germ-is-shift-conjugate-to-a-proper-power` predicts none);
- F: `c(y)^y = c^2(y)`, `c^2(y)^y = c^3(y)`, and `[y, c(y)] ≠ 1`. A hit would embed Thompson's `F` with `x_0`
  acting as the shift, and would give a counterexample;
- the mirror of F with `c^-1`.

Output:
    relA hit: RcwaMapping( [ [ 1, 2, 1 ], [ 1, -2, 1 ] ] )      (a slide, as expected)
    tested 1870 of 1870 candidates; relA hits 28; relP hits 0; F-prototype hits 0; mirror hits 0; t=1616ms

## Reading and blind spots
- The calibration and the planted positives work: 28 relA hits, including the slides.
- The lemma's prediction held: relP had 0 hits.
- No closure and no F prototype were found. This is weak negative evidence only.
- The closure search sees only short-word closures with bounded modulus. The F search sees only products of at most
  2–3 small generators with modulus ≤ 64.
- No run budget remains. A larger search (moduli ≤ 8, longer products, or a Σ^1 computation for specific `Δ`)
  would need new approval.
