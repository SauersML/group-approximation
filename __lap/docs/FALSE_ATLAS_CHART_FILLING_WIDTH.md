# Exact bounded-width fillings of the atlas survivors

Date: 2026-08-11

## 1. Question

Let

\[
 P=A_{8,1}*A_{8,2}\longrightarrow
 Q=L_{\mathbb F _2}(1,2)^\times
\]

be the two-chart atlas.  The all-depth perfect-overlap scan proves that 178
of the 234 first-boundary relators are trivial in the universal central
atlas cover.  Those 178 records collapse to 24 classes under conjugacy and
inversion in the free product.  The remaining 56 records collapse to the
four oriented representatives 11, 30, 44, and 55, and genuine atlas
symmetries leave at most two central classes.

A survivor can still be a product of conjugates of the 24 known-zero
classes.  Such a product would give a multi-chart filling even though no
single chart contains the survivor.  This note tests that possibility by an
exact bounded-width closure.

## 2. Cyclic attachment closure

For a nontrivial free-product word \(w\), let \(\langle w\rangle_c\) denote
its class under free reduction, cyclic conjugacy, and inversion.  Starting
with the 24 certified classes, repeatedly perform

\[
 \langle u\rangle_c,\ \langle s\rangle_c
 \longmapsto \langle us\rangle_c,                    \tag{1}
\]

where \(s\) is certified and every orientation and cyclic rotation of both
words is allowed.  Retain a result only when its cyclically reduced length is
at most \(B\).

Every class produced by `(1)` is zero in the universal central cover:
certified relators are zero, and zero classes are closed under conjugacy,
inversion, and multiplication.  Geometrically, `(1)` attaches one certified
chart cell along the current cyclic boundary.  A positive hit is therefore a
rigorous multi-chart van Kampen certificate.  Failure to hit is deliberately
only a bounded-width statement; a filling may pass through a longer
intermediate boundary or use chart relators outside the first scan.

`experiments/atlas_survivor_chart_filling.py` carries out `(1)`.  It encodes
each \(4\times4\) binary matrix as a 16-bit integer.  Multiplication,
inversion, free reduction, cyclic reduction, and comparison are all exact.
The implementation was cross-checked against the NumPy \(\mathbb F _2\)
arithmetic and the independent free-product reducer on all 27,256
collision-tree words.

## 3. Complete width-eight result

At \(B=8\), the closure stabilizes completely:

| chart cells | new cyclic classes |
|---:|---:|
| 1 | 24 |
| 2 | 222 |
| 3 | 462 |
| 4 | 480 |
| 5 | 148 |
| 6 | 22 |
| 7 | 0 |

Thus the fixed point contains exactly 1,358 cyclic classes.  None of the
four survivor representatives occurs.

**Theorem (width-eight chart-filling obstruction).**  No survivor in the
first atlas boundary can be obtained from the 178 certified
perfect-overlap relators by a sequence of cyclic chart-cell attachments all
of whose intermediate cyclic boundaries have length at most eight.
Consequently every filling admitting such a cyclic attachment ordering, if
one exists, must pass through an intermediate boundary of length at least
ten.

This strengthens the conjugacy-saturated one-chart obstruction: arbitrary
numbers of the known chart cells are allowed, not just one cell or a bounded
number of cells.  It does not prove that either remaining central class is
nonzero in \(R/[P,R]\).

## 4. Width-ten frontier

Width ten is substantially larger.  The first three complete forward layers
have

\[
 24,\qquad 2996,\qquad 10214
\]

new classes, for 13,234 classes in total.  Target-directed reverse layers
from the four survivors contain 292 and 5,200 new tagged classes at depths one
and two.  Neither meets the complete three-cell forward ball.  Thus none of
the four survivors has a width-ten cyclic-attachment filling using at most
five certified cells.  A forward run capped at 20,000 states entered the
fourth layer without finding a survivor, and a reverse run capped at 20,000
states entered its third layer without a meeting, but those capped
calculations are not exhaustive negative results.

## 5. Reproduction

```text
python3 experiments/atlas_perfect_overlap_scan.py \
  --radius 5 --max-leaves 12 --boundary-only \
  --output /tmp/atlas-perfect-overlap.json --summary-only

python3 experiments/atlas_survivor_chart_filling.py \
  /tmp/atlas-perfect-overlap.json \
  --max-boundary 8 --max-cells 10 --max-states 200000 --progress

python3 experiments/atlas_survivor_chart_filling.py \
  /tmp/atlas-perfect-overlap.json \
  --max-boundary 10 --max-cells 3 --max-states 20000 \
  --reverse-steps 2 --max-reverse-states 20000 --progress
```

The next exact multi-chart calculation should either complete the width-ten
closure with a more compact state representation or enlarge the certified
cell set beyond the first radius-ten boundary.  The fixed-dimensional phase
continuation is logically separate: it gives strong evidence for an exact
one-relator phase, whereas this calculation tests whether other known chart
relations already force that phase to vanish.
