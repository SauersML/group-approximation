# Native modular \(A_8\)-modules have no first-order central atlas phase

Date: 2026-08-12

## Result

Let \(P=A_8*A_8\), let \(\mathcal Z_5\) be the 24 cyclic representatives
of the 178 perfect-overlap-certified zero relations, and let

\[
 s_{11},s_{30},s_{44},s_{55}
\]

be the four first-boundary survivor classes.  Identify
\(A_8\cong GL_4(\mathbb F_2)\), and consider the following six
\(\mathbb F_2[A_8]\)-modules:

\[
 V,\quad V^*,\quad \bigwedge^2V,\quad
 \mathbb F_2^{\mathbb P(V)},\quad
 \mathbb F_2^{\mathbb P(V^*)},\quad V\otimes V^*,       \tag{NM1}
\]

of dimensions \(4,4,6,15,15,16\), respectively.  These are the native
modular types already used by the atlas: the defining and contragredient
charts, their exterior square, the point/hyperplane outer-stable pair, and
the endomorphism module.

Use the unique inner alignment \(h\) which kills the complete 234-word
boundary at order zero.  For any finite direct sum \(W\) of the modules in
`(NM1)`, with arbitrary multiplicities, and any
\(X\in\operatorname{End}(W)\), define two charts over
\(D=\mathbb F_2[\varepsilon]/(\varepsilon^2)\) by

\[
 \rho_{1,X}(g)=\sigma(g),\qquad
 \rho_{2,X}(g)=(I+\varepsilon X)
   \sigma(hgh^{-1})(I+\varepsilon X)^{-1}.          \tag{NM2}
\]

**Theorem.** If

\[
 \rho_X(w)=I\quad(w\in\mathcal Z_5)                \tag{NM3}
\]

and each of the four survivor values commutes with the first \(A_8\) chart,
then

\[
 \rho_X(s_{11})=I.                                 \tag{NM4}
\]

Thus no first-order central phase exists in any direct sum of the six native
modular types, even with arbitrary off-diagonal coupling and multiplicity.
In particular, the 30-dimensional point-plus-hyperplane outer-tangent signal
cannot be integrated to first order into the required central phase by
adding any of the other native sectors.

## Exact rectangular-block calculation

At the inner alignment all selected words are identity.  Their
right-trivialized derivatives are binary linear maps \(D_w\).  On every
ordered rectangular block \(X_{ij}\in\operatorname{Hom}(W_j,W_i)\), impose

\[
 D_w(X_{ij})=0\quad(w\in\mathcal Z_5)              \tag{NM5}
\]

and, for every survivor \(s\) and each of the six standard generators \(g\),

\[
 D_s(X_{ij})\sigma_j(g)
 =\sigma_i(g)D_s(X_{ij}).                          \tag{NM6}
\]

Equation `(NM6)` only asks the survivor jet to intertwine the first chart;
it is necessary for centrality and weaker than scalarity.  Exact bitset row
reduction gives the following `rank/nullity` table:

| left \ right | \(V\) | \(V^*\) | \(\wedge^2V\) | points | hyperplanes | \(V\otimes V^*\) |
|---|---:|---:|---:|---:|---:|---:|
| \(V\) | 13/3 | 15/1 | 23/1 | 54/6 | 57/3 | 61/3 |
| \(V^*\) | 15/1 | 13/3 | 23/1 | 57/3 | 54/6 | 61/3 |
| \(\wedge^2V\) | 23/1 | 23/1 | 32/4 | 87/3 | 87/3 | 94/2 |
| points | 57/3 | 54/6 | 87/3 | 211/14 | 210/15 | 231/9 |
| hyperplanes | 54/6 | 57/3 | 87/3 | 210/15 | 211/14 | 231/9 |
| \(V\otimes V^*\) | 61/3 | 61/3 | 94/2 | 231/9 | 231/9 | 244/12 |

For every one of the 36 block types, adjoining all coordinate rows of
\(D_{s_{11}}\) raises the rank by **zero**.  Hence the whole phase block
vanishes on the common kernel of `(NM5)--(NM6)`.  Direct sums and
multiplicities merely repeat these ordered block systems, proving `(NM4)`.

## Scope

This theorem does not classify all modular \(A_8\)-modules and does not rule
out a nonlinear finite extension with different order-zero projective chart
geometry.  It does close the first-order square-zero route in every modular
representation type already native to the atlas calculations.  Combined
with `FALSE_ATLAS_BOOLEAN_DUAL_NO_GO.md`, a remaining modular construction
must introduce a genuinely new indecomposable module or abandon the inner
order-zero alignment.

## Reproduction

```text
PYTHONPATH=experiments \
python3 experiments/atlas_nonboolean_dual_phase_screen.py
```

The verifier constructs every representation in `(NM1)` directly from the
source \(4\times4\) binary matrices, rebuilds the boundary, forms the 36
rectangular systems, and performs exact \(\mathbb F_2\) row reduction.  Its
archived output has SHA-256 hash

```text
bb6a5c869555d132727367f7fa4182c12d1ecdb5a5b4ad7951729f88542adea6
  experiments/atlas-nonboolean-dual-phase-screen.json
```
