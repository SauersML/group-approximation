# Boolean dual-number deformations cannot centralize the full first boundary

Date: 2026-08-11; strengthened 2026-08-12

## Result

Let \(P=A_8*A_8\), let \(\mathcal Z_5\) be the 24 representatives of the
178 perfect-overlap-certified zero relations, and let

\[
 s_{11},s_{30},s_{44},s_{55}
\]

be the four remaining free-product conjugacy/inversion classes.  The exact
finite quotient in `FALSE_ATLAS_DUAL_NUMBER_CENTRAL_QUOTIENT.md` makes
\(s_{11}\) central and nontrivial, but does not centralize the other three
classes.

This note exhausts the most natural enlargement of that construction.
Let \(\Omega_k\) be the set of \(k\)-subsets of an eight-element set and let

\[
 \sigma_k:A_8\longrightarrow GL(\mathbb F _2^{\Omega_k})
\]

be the Boolean permutation representation.  Put

\[
 D=\mathbb F _2[\varepsilon]/(\varepsilon^2)
\]

and use the unique inner alignment \(h\) which kills the complete
234-word first boundary at order zero.  For arbitrary
\(X\in\operatorname{End}(\mathbb F _2^{\Omega_k})\), define

\[
 \rho_{1,X}(g)=\sigma_k(g),
 \qquad
 \rho_{2,X}(g)=(I+\varepsilon X)\sigma_k(hgh^{-1})
                    (I+\varepsilon X)^{-1}.          \tag{BD1}
\]

**Theorem 1 (Boolean dual-number centrality no-go).** Let \(V\) be any
finite direct sum of the Boolean modules

\[
 \mathbb F _2^{\Omega_k},\qquad 1\le k\le7,
\]

with arbitrary multiplicities, and let \(X\in\operatorname{End}(V)\), with
off-diagonal blocks allowed.  If

\[
 \rho_X(w)=I\quad(w\in\mathcal Z_5)                \tag{BD2}
\]

and each of

\[
 \rho_X(s_{11}),\rho_X(s_{30}),
 \rho_X(s_{44}),\rho_X(s_{55})                     \tag{BD3}
\]

commutes with the first \(A_8\) chart, then

\[
 \rho_X(s_{11})=I.                                 \tag{BD4}
\]

In particular, requiring the four survivor values to be central in the
two-chart image forces the desired phase to vanish.  This is stronger than
the earlier scalar-valued statement: it uses the actual relation-module
condition and permits the full modular commutant.

**Theorem 2 (characteristic-two all-order natural-module rigidity).** Put

\[
 D_N=\mathbb F _2[\varepsilon]/(\varepsilon^N).
\]

For every \(N\ge2\), replace \(I+\varepsilon X\) in `(BD1)` by an arbitrary
matrix \(A(\varepsilon)\in GL_8(D_N)\) satisfying \(A(0)=I\).  If all 24
certified words are identity and all four survivors commute with the first
\(A_8\) chart, then

\[
 \rho_A(s_{11})=I.                                \tag{BD4a}
\]

Thus the positive eight-point certificate cannot be promoted to a complete
central-boundary model by changing subset degree, adding Boolean permutation
sectors or multiplicity at first order, nor by passing to higher univariate
dual numbers in the natural module. The natural-module conclusion has since
been extended from characteristic two to every coefficient field in
`FALSE_ATLAS_NATURAL_ALL_FIELD_HIGHER_ORDER_NO_GO.md`.

## Exact linearization

At the alignment \(h\), every selected word has value \(I\).  If
\(w=A_1\cdots A_m\), with prefix products \(P_j=A_1\cdots A_j\), then in
characteristic two

\[
 \rho_X(w)=I+\varepsilon D_w(X),
\]

where

\[
 D_w(X)=
 \sum_{\substack{1\le j\le m\\A_j\text{ from chart }2}}
 \left(\operatorname{Ad}(P_{j-1})+
       \operatorname{Ad}(P_j)\right)X.              \tag{BD5}
\]

Every \(P_j\) is a permutation matrix, so `(BD5)` is a binary linear map
whose rows are represented exactly by bitsets.  Conditions `(BD2)` say that
all entries of the corresponding derivatives vanish.  Centrality is weakened
to commutation with the first chart: on a rectangular block
\(X_{ij}\in\operatorname{Hom}(V_j,V_i)\), it requires

\[
 D_s(X_{ij})\sigma_j(g)
 =\sigma_i(g)D_s(X_{ij})                         \tag{BD5a}
\]

for the six standard chart generators \(g\) and each survivor \(s\).
This is necessary for full centrality and is strictly weaker than scalarity.

Exact row reduction for all 16 ordered block types gives:

| \(i\backslash j\) | 1 | 2 | 3 | 4 |
|---:|---:|---:|---:|---:|
| 1 | 61/3 | 219/5 | 440/8 | 550/10 |
| 2 | 219/5 | 768/16 | 1548/20 | 1931/29 |
| 3 | 440/8 | 1548/20 | 3101/35 | 3878/42 |
| 4 | 550/10 | 1931/29 | 3878/42 | 4839/61 |

Each entry is `constraint rank/nullity` on
\(\operatorname{Hom}(\mathbb F_2^{\Omega_j},
\mathbb F_2^{\Omega_i})\).  In every block, adjoining all entries of
\(D_{s_{11}}\) raises the rank by zero.  Hence the **whole phase block**
vanishes on the constraint kernel.  Complementation identifies degrees
\(k\) and \(8-k\); repeated summands repeat the same rectangular systems.
This proves Theorem 1, including arbitrary multiplicities and off-diagonal
blocks.

## Quadratic obstruction and all higher dual numbers

For the natural eight-point module the first-order system has rank 61 and
nullity three.  Over
\(\mathbb F_2[\varepsilon]/(\varepsilon^3)\), write the relative factor as

\[
 I+\varepsilon X+\varepsilon^2Y.                 \tag{BD5b}
\]

All eight possible first-order classes \(X\) were exhausted.  Exactly four
extend to a solution at order two.  They have matrix weights

\[
 0,\ 8,\ 56,\ 64
\]

and are precisely the four matrices in the two-dimensional chart commutant
\(\langle I,J\rangle_{\mathbb F_2}\).  All four have zero second-order
phase.  The other four first-order classes, of weights

\[
 20,\ 28,\ 36,\ 44,
\]

have inconsistent affine equations for \(Y\).  Thus every noncommutant
first jet is quadratically obstructed.

To deduce Theorem 2, right-multiply \(A(\varepsilon)\) by an invertible
commutant-valued series; this does not change the conjugated second chart.
It can remove all commutant coefficients preceding the first noncommutant
coefficient \(X_m\varepsilon^m\).  Below order \(2m\), the equations are the
homogeneous first-order system, so Theorem 1 makes every phase coefficient
zero.  At order \(2m\), when that order exists in \(D_N\), the quadratic
calculation above says that \(X_m\) cannot extend.  If \(2m\ge N\), every
visible phase coefficient has already vanished.  In either case `(BD4a)`
follows.

## Why quotienting the positive finite image must fail

The obstruction is already visible inside the positive finite image

\[
 H=(C_2)^7\rtimes A_8
\]

from the previous certificate.  In its dual-number realization,

\[
 \rho(s_{30})
 =I+\varepsilon\operatorname{diag}(1,1,1,0,0,0,1,0). \tag{BD6}
\]

Let \(g=p_{1,01}\) be the first standard chart transvection.  In the
natural eight-point action it is

\[
 (0\ 5)(1\ 3)(2\ 4)(6\ 7),                         \tag{BD7}
\]

which carries the four-element support in `(BD6)` to its complement.
Both \(\rho(s_{30})\) and \(\rho(g)\) are involutions, and exact
dual-number multiplication gives

\[
 [\rho(s_{30}),\rho(g)]
 =(1+\varepsilon)I
 =\rho(s_{11}).                                    \tag{BD8}
\]

Consequently every quotient of \(H\) in which \(s_{30}\) becomes central
also kills the desired phase \(s_{11}\).  The positive certificate is
therefore intrinsically a one-central-class certificate; its failure on the
second class cannot be repaired by taking a quotient of its finite image.

## Scope and next construction

These are exact no-go theorems for a broad and natural modular family, not a
no-go theorem for the full FALSE program.  The next positive target must
leave at least one of the following restrictions:

1. Boolean permutation modules of the natural eight-point action;
2. a one-parameter local deformation of the natural module;
3. the inner alignment which collapses both charts at order zero; or
4. promotion by quotienting \((C_2)^7\rtimes A_8\).

The live alternatives are a genuinely nonlinear finite extension with
different projective chart geometry, or a deformation in a non-Boolean
modular representation.  Merely increasing the truncation order of the
natural eight-point construction is now rigorously exhausted.

## Reproduction

```text
PYTHONPATH=experiments \
python3 experiments/atlas_subset_dual_central_no_go.py

PYTHONPATH=experiments \
python3 experiments/atlas_subset_dual_commutant_phase.py

PYTHONPATH=experiments \
python3 experiments/atlas_natural_second_order_no_go.py
```

The verifiers reconstruct \(GL_4(2)\cong A_8\), rebuild the original atlas
words, form every row of `(BD5)` directly from prefix permutations, perform
exact \(\mathbb F _2\) bitset elimination, check all 16 rectangular systems,
exhaust the eight natural-module first jets at order two, and verify the
commutator identity `(BD8)`.  The archived outputs have SHA-256 hashes

```text
50034741480fa4d2ecc249b4c2583c7e8dd9d4d1c7315902557ce9c0d21b62ef
  experiments/atlas-subset-dual-commutant-phase.json
318907495f2a271e1b6339103d4e24b1d795478fa5e6d1efbcd4fad5ab304d24
  experiments/atlas-natural-second-order-no-go.json
```
