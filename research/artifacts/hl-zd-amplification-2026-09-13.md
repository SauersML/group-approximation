# Quasimorphism amplification for support-three zero divisors (lane hl-zd-amplification, 2026-09-13)

Target: gap (b) of `research/artifacts/hl-zero-divisor-2026-09-13.md` §4. Show that a
support-three zero divisor forces `phi = 0` on `x`, `y`, `x^-1 y` for every homogeneous
quasimorphism. That would settle support three in torsion-free hosts with positive scl on
nontrivial elements, including torsion-free hyperbolic groups, and answer Steenbock's
question (arXiv:1307.0981, introduction l.120, "Do Rips-Segev groups satisfy Kaplansky's
zero-divisor conjecture?") at support three.

**Verdict: partial.** The target is not reached. Two results landed (ESTABLISHED, not
independently reviewed, no novelty claimed): a sharper bound, and a barrier showing the
target cannot follow from the positive relations, which are the only input of the landed
bounds.

## 1. Landed

| id | content |
|---|---|
| `support-three-zero-divisor-quasimorphism-bound-five-thirds` | syllable lemma; `|phi| <= 5D/3` on the differences (was `3D`); `scl <= 5/6`; `5/3` optimal for the inequalities used |
| `three-positive-relations-allow-positive-scl` | explicit torsion-free hyperbolic `C'(1/6)` group with all three positive relations, `H_1 = 0`, and nonzero quasimorphisms on all three differences |
| `calegari-fujiwara-gap-theorem-strong-version` | import: torsion-free hyperbolic groups carry `h` with `h(a) = 1` for each nontrivial `a` (arXiv:math/0611889, Theorem A′, remark on mirrors, Bavard duality) |
| `cprime-one-sixth-presentations-hyperbolic-and-torsion-free` | import: finite classical `C'(1/6)` with no proper power gives aspherical, torsion-free, hyperbolic (arXiv:1210.0178) |

## 2. Amplification attempts (none works)

1. **Frobenius.** `(1 + x + y)^2 = 1 + x^2 + y^2 + xy + yx` over `F_2`, support five unless
   `xy = yx`, and then `<x, y>` is abelian, where there is no zero divisor. Not
   support-preserving.
2. **Finite-index restriction.** `alpha` becomes a matrix over `k[H]`; no support-three
   element.
3. **Homomorphisms `G -> G'`.** Pulling back `phi` keeps the ratio `phi(d)/D(phi)` bounded
   by the same constant; nothing rescales.
4. **Syllables.** A positive relation with `s` blocks of each letter has error `(2s - 1)D`
   against letter counts `i, j >= s`. This gives the `5/3` bound. Amplifying to `0` would need
   cycles of the Kaplansky functional graphs with `i/s, j/s -> infinity`. But the maximal
   `x`-chains `b, xb, ..., x^L b` in `B` partition `B` into `|B| - |X| = n/2` chains (the
   partial map `b -> xb` has `n/2` edges and no cycles, `x` having infinite order), so chains
   have average size `2`, and no long runs are forced.
5. **Flow sums.** For the partial maps `X: b -> xb`, `Y: b -> yb`, `Z: b -> y^-1 x b`, sum
   `phi(target) - phi(source)` over edges of each: `(n/2)(phi(label) +- D)`. With
   `i_X + i_Y = 1`, `o_X + o_Z = 1`, `o_Y + i_Z = 1` at every vertex, the vertex coefficients
   of `alpha S_X + beta S_Y + gamma S_Z` vanish identically only for
   `alpha = beta = gamma = 0`. No constraint on `(a, b, c)` follows.
6. **Maximum principle.** At a vertex of `B` maximising `phi`, the three degree identities
   reproduce the cone disjunctions already landed (`zero-divisor-supports-have-no-quasimorphism-isolated-extremes`).

## 3. The barrier

`three-positive-relations-allow-positive-scl`: every input of the `3D` and `5D/3` proofs holds
in an explicit torsion-free hyperbolic group where quasimorphisms do not vanish on the
differences. In that group `0 < scl <= 5/6` on `x`, `y`, `x^-1 y`.

**Search record.** `sc_search.py` samples relators built from syllables (`R_1` in `x, y`, `R_2`
in `x, Yx`, `R_3` in `y, Xy`, exponents `1..4`, `k` syllable pairs), and computes the largest
piece ratio exactly. MSI array job `739057` (8 tasks, all COMPLETED 0:0):

| seed | k | best ratio | C'(1/6) | lengths |
|---|---|---|---|---|
| 1 | 12 | 0.1807 | no | 62, 88, 83 |
| 2 | 14 | 0.1600 | yes | 63, 110, 100 |
| 3 | 16 | 0.1429 | yes | 77, 120, 119 |
| 4 | 18 | 0.1594 | yes | 94, 138, 146 |
| 5 | 20 | 0.1538 | yes | 90, 160, 156 |
| 6 | 22 | 0.1455 | yes | 110, 156, 137 |
| 7 | 24 | 0.1538 | yes | 117, 182, 172 |
| 8 | 26 | 0.1230 | yes | 135, 182, 187 |

Seed `3` was certified by two independent programs (`sc_verify.py`, `sc_verify_hash.py`). Files
in `research/artifacts/hl-zd-amplification-2026-09-13/`: the three scripts, `run.sbatch`,
`seed3.json`, `verify3.txt`, `verify3_hash.txt`, `search-census.txt`.

## 4. Hyperbolic case (directive step 2)

- Calegari–Fujiwara give `h(d) = 1` with `D(h) <= C(delta, |S|)`, so `scl(d) >= 1/(2C)`. The
  `5D/3` bound excludes a triple only if `scl(d) > 5/6`. The gap constant is not that large in
  general, so the gap theorem alone excludes nothing.
- Delzant: hyperbolic groups acting with large translation length have unique products
  (quoted in Steenbock, arXiv:1307.0981, l.108–109 and l.159–160). Rips–Segev groups admit no
  such action, which is why they are the test case.

## 5. Exact gap

- **Use of `B`.** A quasimorphism argument must use the three unicyclic functional graphs on
  the finite cofactor `B` beyond their cycle relations. The barrier group has all the relations,
  and no cofactor is known in it.
- **Concrete target.** In a torsion-free host, show a support-three zero divisor forces some
  difference `d` to satisfy `phi(d) = 0` for all homogeneous `phi` (equivalently, for
  `d in [G, G]`, `scl(d) = 0`). In torsion-free hyperbolic hosts that is nonexistence at
  support three.
- **Test group.** `G` of the barrier: any argument claiming (b) must fail to produce a cofactor
  `B` there; a proof that `F_2[G]` has no support-three zero divisor with differences `x, y`
  would be a first check of a candidate method.
