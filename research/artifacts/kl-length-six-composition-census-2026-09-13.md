# KL length-six torsion residue: exhaustive composition census

Lane `hl-kl-short-equations`, 2026-09-13. Target:
`kl-length-six-coincidence-saturated-torsion-residue`, after
`kl-length-six-residue-words-with-hyperlinear-coefficients-inject` (22de3cc6b).

**Question.** Can an open involution-loop residue word be written as
`sigma_u(v)`, with `v` nonsingular in the variable `z` and `u` a nonsingular
inner word of variable length at most five? If so,
`kl-substituting-a-short-inner-word-preserves-injectivity` settles it over every
group, provided the outer word `v` is itself settled by the length-at-most-five
theorem.

**Answer at the tested sizes: no.** The only compositions found are the already
settled `++++--` families `(1,1,1)` and `(1,g,1)`, with `u = t^(+-2)`. These are
the controls.

## Model

- **Coefficient group:** the free product `Z * C_2 * C_2`, with free generator `g`
  and involutions `x`, `y` (case INV). In case REL it is `Z * C_2`, with
  `y := g x g^(-1)`.
- **Why a hit is universal:** an identity in this model holds in every group with
  involution loops (INV), resp. every group where `y = g x g^(-1)` (REL).
- **Why a miss is weaker:** a miss only rules out identities that hold in the free
  model. It says nothing about identities that need extra relations among `g`,
  `x`, `y`.

## Targets

- **INV:** the fourteen normalized residue shapes of the residue node, plus the
  two settled `++++--` controls `(1,1,1)` and `(1,g,1)`.
- **REL:** the four three-equal `+++++-` shapes with `y = g x g^(-1)`.

In both cases the relator's inverse is matched too, and a match counts only up to
cyclic conjugacy.

## Search space

- **Outer word:** `v = z^(e_1) d_1 z^(e_2) d_2 ... z^(e_K) d_K`.
- **Inner word:** `u = t^(f_1) c_1 ... c_(M-1) t^(f_M)`.
- **Signs and coefficients:** all signs `e_i, f_j` in `{+-1}`, and all
  coefficients reduced words of length at most `L` in `g^(+-1), x, y`.
- **Constraint:** `|deg v| * |deg u|` equals the degree of the target.

| Case | K | M | L | tested pairs | non-control hits |
|---|---|---|---|---|---|
| INV | 3 | 2 | 2 | 887,808 | 0 (24 control hits) |
| INV | 2 | 3 | 2 | 924,800 | 0 |
| INV | 4 | 2 | 2 | 20,123,648 | 0 |
| INV | 2 | 4 | 1 | 36,000 | 0 |
| INV | 3 | 4 | 1 | 465,600 | 0 |
| INV | 4 | 3 | 1 | 498,400 | 0 |
| INV | 2 | 5 | 1 | 373,600 | 0 |
| INV | 5 | 2 | 1 | 328,000 | 0 |
| INV | 4 | 4 | 1 | 2,304,000 | 0 |
| REL | 4 | 2 | 2 | 1,296,000 | 0 |
| REL | 2 | 4 | 1 | 10,752 | 0 |
| REL | 3 | 4 | 1 | 27,648 | 0 |
| REL | 4 | 3 | 1 | 33,792 | 0 |
| REL | 4 | 4 | 1 | 387,072 | 0 |

MSI array job 731699, all tasks COMPLETED exit 0. The per-task lines are in
`kl-length-six-composition-census/output-2026-09-13.txt`, and the script is
`compsearch.py` (md5 `9d85ba6e651e2888c3acfbd57aca5238`).

## Scope

- **Conjugating the inner word.** `u` carries no outer coefficients. Replacing `u`
  by `c u c^(-1)` conjugates `sigma_u(v)` after conjugating the coefficients of
  `v` by `c`. So words `u` with outer coefficients are covered only when those
  conjugated coefficients still have length at most `L`.
- **Fifth-power compositions.** The table has no `(K, M) = (5, 5)` row, and
  `L = 1` is used from `M = 4` on.
- **Consistency check.** The hand count in the residue node finds compositions
  only when `g` equals a loop coefficient or its inverse. The free model excludes
  that, so zero hits is the expected outcome and matches it.

## Consequence

For the involution-open shapes that
`kl-length-six-residue-words-with-hyperlinear-coefficients-inject` leaves, `g`
lies outside `<x, y>`, and in the REL case `y = g x g^(-1)`. Within the table's
bounds, no substitution certificate exists for these shapes in the free model.
What remains is a picture argument, or a certificate that uses relations beyond
the free model.
