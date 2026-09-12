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

| Shape | Settled | Open |
|---|---|---|
| `(1,1,1,1)` | `<x,y>` hyperlinear, including involution loops | other torsion with `<x,y>` not known hyperlinear |
| `(1,1,g,1)`, `(1,g,1,1)` | weight regimes; involution loops under (I1)-(I4); `g` equal to the adjacent loop by substitution | involution loops with `g x g^-1 = y`, `g = y x` or `g^2 x g^-1 y = 1`; orders `(2, finite > 2)`, `(3,3)`, `(3,4)`, `(3,5)` |
| `(1,1,1,g)`, `(g,1,1,1)` | weight regimes; `g = x^-1`, resp. `g = y^-1`, by substitution | involution loops; the small finite orders above |
| two-pair `+++++-` | nothing new | every torsion order |
| `(1,1,g)`, `(g,1,1)`, `(g,g,g)` | weight regimes | involution loops; small finite orders |
| two-pair `++++--` | nothing new | every torsion order |

With involution loops, the Leavitt case, the open shapes are:
- `(1,1,1,g)` and `(g,1,1,1)`;
- the three `+++++-` two-pair shapes;
- all six `++++--` shapes;
- `(1,1,g,1)` and `(1,g,1,1)` only on the three special relations.

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
- In `++++--` the receivers are pairs of same-sign corners `(a_3, n)` and
  `(n, a_1)`. The N-corner can sit in two transfer pairs, so the heavy-corner
  count does not bound the transfers.

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

This is a finite enumeration, landed as an orientation document, not a Cairn
claim.
