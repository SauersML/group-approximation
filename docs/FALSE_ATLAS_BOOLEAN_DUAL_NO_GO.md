# Boolean dual-number deformations cannot centralize the full first boundary

Date: 2026-08-11

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

**Theorem 1 (Boolean dual-number no-go).** For every \(1\le k\le7\), if

\[
 \rho_X(w)=I\quad(w\in\mathcal Z_5)                \tag{BD2}
\]

and each of

\[
 \rho_X(s_{11}),\rho_X(s_{30}),
 \rho_X(s_{44}),\rho_X(s_{55})                     \tag{BD3}
\]

is scalar, then

\[
 \rho_X(s_{11})=I.                                 \tag{BD4}
\]

The same conclusion holds for arbitrary finite direct sums and
multiplicity amplifications of the Boolean subset representations, even
when \(X\) has off-diagonal blocks between the summands.

Thus the positive eight-point dual-number certificate cannot be promoted to
a model of the complete first central boundary by changing the subset
degree, adding Boolean permutation sectors, or adding multiplicity.

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
all entries of the corresponding derivatives vanish.  Conditions `(BD3)`
say that every off-diagonal entry vanishes and all diagonal entries are
equal.  Finally, after these scalarity equations are imposed, the
upper-left entry of \(D_{s_{11}}(X)\) is the possible scalar phase.

Exact row reduction gives:

| \(k\) | \(|\Omega_k|\) | \(\dim\operatorname{End}\) | constraint rank | nullity | phase row modulo constraint span |
|---:|---:|---:|---:|---:|---:|
| 1 | 8 | 64 | 61 | 3 | 0 |
| 2 | 28 | 784 | 768 | 16 | 0 |
| 3 | 56 | 3136 | 3101 | 35 | 0 |
| 4 | 70 | 4900 | 4839 | 61 | 0 |

The final column is the decisive certificate: the scalar phase functional
belongs to the row span of the zero and centrality equations.  It therefore
vanishes on their common kernel.  Complementation identifies the actions on
\(k\)-subsets and \((8-k)\)-subsets, proving the result for \(k=5,6,7\).

For a direct sum \(V=\bigoplus_iV_i\), the maps `(BD5)` preserve every
block \(\operatorname{Hom}(V_j,V_i)\).  A scalar value of the phase has zero
off-diagonal blocks, while each diagonal block must have the same scalar.
The table forces that scalar to be zero on every diagonal block.  This proves
the direct-sum and multiplicity assertion.

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

This is an exact no-go theorem for a broad and natural modular family, not a
no-go theorem for the full FALSE program.  It says that the next positive
target must leave at least one of the following restrictions:

1. first-order square-zero deformation;
2. Boolean permutation modules of the natural eight-point action;
3. the inner alignment which collapses both charts at order zero; or
4. promotion by quotienting \((C_2)^7\rtimes A_8\).

The live alternatives are a genuinely nonlinear finite extension with
different projective chart geometry, or a higher-order deformation in a
non-Boolean modular representation.  In particular, repeating the
eight-point construction at larger subset degree is now rigorously
exhausted.

## Reproduction

```text
PYTHONPATH=experiments \
python3 experiments/atlas_subset_dual_central_no_go.py
```

The verifier reconstructs \(GL_4(2)\cong A_8\), rebuilds the original atlas
words, forms every row of `(BD5)` directly from prefix permutations, performs
exact \(\mathbb F _2\) bitset elimination, checks all four ranks in the
table, and verifies the commutator identity `(BD8)`.
