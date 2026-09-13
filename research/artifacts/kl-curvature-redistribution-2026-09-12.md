# KL length-six torsion residue: fences, curvature map and small-picture census

Lane `kl-curvature-redistribution`, 2026-09-12. Target: the open claim
`kl-length-six-coincidence-saturated-torsion-residue`, whose normalized residue
shapes are:
- `+++++-`: `(1,1,1,1)`; the three-equal shapes `(1,1,1,g)`, `(1,1,g,1)`,
  `(1,g,1,1)`, `(g,1,1,1)`; the two-pair shapes `(1,1,g,g)`, `(1,g,1,g)`, `(1,g,g,1)`.
- `++++--` (N-label `1`): `(1,1,g)`, `(g,1,1)`, `(g,g,g)`, and the two-pair shapes
  `(1,g,g)`, `(g,g,1)`, `(g,1,g)`.

In every shape the loops `y` (at `t^-`) and `x` (at `t^+`) are nontrivial, and at
least one has finite order. The node lists eight `+++++-` shapes, not seven.

## 1. What landed

| Commit | Node | Content |
|---|---|---|
| bfa2e6677 | `kl-substituting-a-short-inner-word-preserves-injectivity` | `v(u)` injects if `v` does and `u` is nonsingular with `ell_t(u) <= 5` |
| bfa2e6677 | `kl-length-six-residue-squares-and-fourth-powers-inject` | `+++++-` words equal to `u^2 c` or `u^4 c` inject; residue sub-cases `(1,1,g,1)` with `g = y`, `(g,1,1,1)` with `g = y^-1`, `(1,g,1,1)` with `g = x`, `(1,1,1,g)` with `g = x^-1`, for every loop order |
| bfa2e6677 | `kl-two-coefficient-residue-word-with-involution-loops-injects` | `t^5 y t^-1 x` injects when `<x, y>` is hyperlinear, e.g. with involution loops |
| 78565c273 | residue node Attempts | the composition count, and which shapes stay open with involution loops |
| 2cf7bde45 | `kl-three-coincidence-residue-words-inject-with-room-for-loops` | weight test for the seven three-coincidence shapes, whenever `2/k_y + 2/k_x <= 1` and `g` avoids short loop words |
| a63352293 | `kl-involution-loop-residue-with-interior-light-label-injects` | curvature redistribution for `(1,1,g,1)` and `(1,g,1,1)` with involution loops, under four generic relations |
| ee349909c | `kl-three-equal-residue-shapes-inject-for-every-loop-order` | one-sided loop weights settle the four three-equal `+++++-` shapes for every loop order, under (X1)-(X3) or (Y1)-(Y3); lane `kl-remaining-shapes` |

Cairn on MSI, in a `--shared` clone at the tip with the nodes overlaid:
- `check --changed` exits 0;
- it unlocks only the new claims;
- the residue claim, `kervaire-laudenbach-nonsingular-conjecture`,
  `kl-violating-equation-over-leavitt-unit-group` and `non-hyperlinear-group`
  stay OPEN.

## 2. Status by shape and loop orders

"Weight" means `kl-three-coincidence-residue-words-inject-with-room-for-loops`:
- one loop of infinite order and `g` outside its cyclic subgroup; or
- both orders finite with `2/k_y + 2/k_x <= 1`, under (C1)-(C2).

"One-sided" means `kl-three-equal-residue-shapes-inject-for-every-loop-order`:
every loop order, under (X1)-(X3) when `a_1 = 1`, or (Y1)-(Y3) when `a_4 = 1`.

"Small finite orders" means both orders finite with `2/k_y + 2/k_x > 1`: one loop
of order two, or orders `3` and `3`, `4` or `5`.

| Shape | Settled | Open |
|---|---|---|
| `(1,1,1,1)` | `<x,y>` hyperlinear, including involution loops | other torsion with `<x,y>` not known hyperlinear |
| `(1,1,g,1)`, `(1,g,1,1)` | weight regimes; one-sided, under (X1)-(X3) or (Y1)-(Y3); `g = y`, resp. `g = x`, by substitution | involution loops with `g = x`, resp. `g = y`, or `g = y x`, or `g x g^-1 = y`; small finite orders where one of (X1)-(X3) and one of (Y1)-(Y3) fail |
| `(1,1,1,g)`, `(g,1,1,1)` | weight regimes; one-sided, under (X1)-(X3), resp. (Y1)-(Y3); `g = x^-1`, resp. `g = y^-1`, by substitution | involution loops with `g = y`, resp. `g = x`, or `g = y x`, or `g x g^-1 = y`; small finite orders where (X1)-(X3), resp. (Y1)-(Y3), fail |
| two-pair `+++++-` | nothing new; one-sided weights leave both loops at weight zero | every torsion order |
| `(1,1,g)`, `(g,1,1)`, `(g,g,g)` | weight regimes | involution loops; small finite orders; one-sided weights fail at the N-corner |
| two-pair `++++--` | nothing new | every torsion order |

With involution loops, the Leavitt case, the open shapes are:
- the four three-equal `+++++-` shapes, each only on three relations:
  - `(1,1,1,g)` and `(1,g,1,1)`: `g = y`, `g = y x`, `g x g^-1 = y`;
  - `(g,1,1,1)` and `(1,1,g,1)`: `g = x`, `g = y x`, `g x g^-1 = y`;
- the three `+++++-` two-pair shapes;
- all six `++++--` shapes.

## 3. Curvature map

**Budget.** The relative weight test has budget `n - 2 = 4`.
- A trivial 2-cycle between two heavy same-sign corners costs total weight two.
- A loop of order `k` needs weight at least `2/k`.

The shape families spend the budget as follows:
- **`(1,1,1,1)`**: four pairwise heavy corners cost four, so no torsion loop fits.
- **Three-coincidence shapes**: a pairwise heavy triple costs three, leaving one
  unit for the two loops. This is where `2/k_y + 2/k_x <= 1` comes from.
- **Two-pair shapes**: two disjoint pairs cost four, so no torsion loop fits.

**Where torsion forces positive curvature.** Weight the heavy corners `1`, the
light corner `0`, and split the leftover among the loops. The regions of weight
below two, i.e. positive curvature `2 pi - pi W`, are then:
- loop powers `y^k`, `x^k` whose weight `k theta` is below two. With involution
  loops and `theta = 1/2` these are the squares `y^2`, `x^2` of weight one;
- short mixed cycles whose labels are relations between `g` and the loops. For
  the P-light shapes with involution loops these are exactly:
  - `g in {x, y}` (weight `3/2`);
  - `g x g^-1 = y` (weight one);
  - `g = y x`, and `g^2 x g^-1 y = 1`: weight two, which matters only for regions
    that receive transferred curvature.

This list was cross-checked on MSI by enumerating all reduced star-graph cycles
up to length eight in `C_2 * C_2 * Z`, by `claim_a_report` in the census script.

**Where the redistribution lands.** A `y^2` region between discs `D_1`, `D_2`
has two arcs. The regions across them contain the consecutive corners
`(c_3 of D_1, x of D_2)` and `(c_3 of D_2, x of D_1)`. An `x^2` region's
neighbours contain `(y, c_0)`.
- In `+++++-` shapes with `c_0` and `c_3` heavy, `(1,1,g,1)` and `(1,g,1,1)`,
  every receiver gains a heavy corner and a loop corner per transfer, and the
  count closes.
- In `(1,1,1,g)` and `(g,1,1,1)` one family of transfers lands next to the light
  corner. A region such as `g x^2 g^-1 y^2` can receive two transfers with
  weight two.
- **One-sided weights avoid this** (lane `kl-remaining-shapes`).
  - With all the loop weight on `y`, only `x`-regions give, and their receivers
    contain `(y, c_0)` at weight two.
  - With all the loop weight on `x`, only `y`-regions give, and their receivers
    contain `(c_3, x)` at weight two.
  - So the light corner never lies in a receiving pair when `a_1 = 1`, resp.
    `a_4 = 1`.
- In `++++--` the receivers are pairs of same-sign corners `(a_3, n)` and
  `(n, a_1)`. The N-corner can sit in two transfer pairs, so the heavy-corner
  count does not bound the transfers. One-sided weights fail there too:
  - with the weight on `y`, the trivial region `n a_1 x^(k_x)` of `(1,1,g)` has
    weight two and can take `pi`;
  - with the weight on `x`, the receiver `(a_3, n)` of `(1,1,g)` has only weight
    one.

**Degree-two corners per disc** (census column `maxdeg2`: the largest compatible
set of corners of one disc in degree-two faces). With involution loops it is `4`
for `(1,1,1,1)`, `(1,g,g)` and `(g,g,1)`, and `3` for every other shape. With the
angle `2 pi/d` convention a disc with `m` degree-two corners and all others of
degree at least four has curvature at most `pi (m - 2)/2`. So every disc with
three degree-two corners is a potential positive vertex; this is the entry point
for a vertex-based redistribution in the open shapes.

## 4. Small-picture census

Artifacts:
- `research/artifacts/kl-residue-picture-census/pairings.c`;
- `census.py`, `lstar_scan.py`, `census-output-2026-09-12.txt`.

`pairings.c` enumerates every pairing of the letters of `area` relator discs,
half positive and half negative (sign balance forces this). It keeps those that
are:
- dipole-free: no arc joins occurrence `i` of `w` to the inverse occurrence
  `5 - i` of `w^-1`;
- connected;
- of genus zero: `F = 2 + 2V`.

It deduplicates by relabelling discs of equal orientation.

| Class | Area 2 | Area 4 (dipole-free complete pairings / planar / up to relabelling) |
|---|---|---|
| `+++++-` | 12 | 59,245,120 / 14,056 / 3,604 |
| `++++--` | 13 | 59,245,120 / 22,238 / 5,657 |

`census.py` evaluates face labels in `U = Z(g) * C_(k_y)(y) * C_(k_x)(x)` for
all 14 shapes. Loop orders:
`(2,2)`, `(2,inf)`, `(inf,2)`, `(3,inf)`, `(inf,3)`, `(2,3)`, `(3,2)`, `(3,3)`,
`(4,inf)`, `(inf,4)`, `(6,inf)`, `(inf,6)`.

**Result.** In every case no reduced pairing of area two or four has all faces
trivial, or all but one. So a coefficient-boundary picture over the universal
model needs area at least six. Over an actual group `G`, a violation of area at
most four needs extra coefficient relations: at least
`min_nontriv - 1` of them, where `min_nontriv` is the fewest nontrivial faces:
- `1` at area four for `(1,1,1,1)` with involution loops, a shape already
  settled for dihedral `<x,y>`;
- `2` or more in every other case;
- `5` for `(g,1,g)`.

**Control.** With the dipole test switched off (`pairings <class> 2 keep`), area
two has 17 planar pairings for `+++++-` and 23 for `++++--`. For every shape
exactly one has all faces trivial: the complete gluing of `w` to `w^-1`. So the
corner and orientation conventions reproduce the one picture that must exist
(`CONTROL_PASS`).

This is a finite enumeration, landed as an orientation document, not a Cairn
claim. The full output is `kl-residue-picture-census/census-output-2026-09-12.txt`.

## 5. Scan over the binary Leavitt unit group

`lstar_scan.py` evaluates, in `R^x = L_(F_2)(1,2)^x`, every face label of every
reduced planar pairing of area two and four. It uses the shared exact normal
form `experiments/nonsofic-certificates/leavitt.py`, with the dual check off for
the search and on for rechecking hits. It runs for the 13 shapes still open with
involution loops. Face words are first reduced in `Z(g) * C_2(x) * C_2(y)`,
which is valid in any group where `x` and `y` are involutions, so that side
costs nothing.

**First pass** (acn112, 12 seconds):
- involutions `x, y in {u, v, w, u^g, v^g, swap(00,01)}`;
- labels `g in {g3, x0, x1, uw, vw, rot3}`.

Here `u = 1+s0t1`, `v = 1+s1t0`, `w = s0t1+s1t0`, `g3 = uv`; `x0`, `x1` are
Thompson `F` generators and `rot3` the order-three Thompson rotation. That is
216 triples per shape, 3,616 pairings (`+++++-`) or 5,670 (`++++--`).

- **Candidate hits:** none. No pairing has at most one nontrivial face in `R^x`.
- **Fewest nontrivial faces:** 2 for `(1,1,1,g)`, `(1,1,g,g)` and `(g,1,1,1)`;
  4 for the other ten shapes.

So over these coefficients a violation needs area at least six.

**Larger pass** (`lstar_scan.py 1200 big`, acn112, 793 seconds):
- 24 involutions: conjugates of `u`, `v`, `w`, `swap(00,01)`, `swap(10,11)`,
  `swap(0,10)` by `g3`, `rot3`, `u`, `uw`, `v`, `w`, `x0`, `x1`, deduplicated;
- 24 labels: `g3`, `x0`, `x1`, `uw`, `vw`, `rot3`, and products of pairs;
- all 13,824 triples for each of the 13 shapes.

Results:
- **Candidate hits:** none.
- **Fewest nontrivial faces:** 2 for `(1,1,1,g)`, `(1,1,g,g)` and `(g,1,1,1)`; 4
  for the other ten shapes.
- **Minimizer:** in all three shapes the first minimizer is `g = g3`, `x = u`,
  `y = u^uw`, at area four. Two faces die in `R^x` but not in `U`, both
  conjugates of the relation `g = y x`. The two surviving faces are `g^(+-1)`.
  So the nearest templates come from the relation `g = y x`, which (I3)
  already singles out as the boundary case of the curvature count.

**Reading.** Over the 24 x 24 x 24 coefficient lists, no Kervaire--Laudenbach
certificate over `R^x` has at most four relator discs. A search for a violation
has to go to area at least six, where brute-force pairing is infeasible (18
arcs); planar-map generation would be needed.
