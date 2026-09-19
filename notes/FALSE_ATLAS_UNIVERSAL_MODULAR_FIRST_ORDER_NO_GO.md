# Universal modular first-order atlas no-go

Date: 2026-08-12

## Theorem

Let (G=A_8\cong GL_4(\mathbb F_2)), let (P=G*G), and use the unique
inner alignment which kills the complete 234-word first boundary at order
zero.  Let \(\mathcal Z_5\) be the 24 cyclic representatives of the 178
perfect-overlap-certified zero relations, and put

\[
 \mathcal S=\{s_{11},s_{30},s_{44},s_{55}\}.
\]

Let (W) be **any** finite-dimensional \(\mathbb F_2[G]\)-module and let
\(X\in\operatorname{End}_{\mathbb F_2}(W)\).  Over
\(D=\mathbb F_2[\varepsilon]/(\varepsilon^2)\), form the two charts

\[
 \rho_{1,X}(g)=\sigma(g),\qquad
 \rho_{2,X}(g)=(I+\varepsilon X)
   \sigma(hgh^{-1})(I+\varepsilon X)^{-1},             \tag{UM1}
\]

where (h\in G) is the fixed inner alignment.

**Universal no-go.**  Assume

\[
 \rho_X(z)=I\quad(z\in\mathcal Z_5)                   \tag{UM2}
\]

and every value \(\rho_X(s)\), \(s\in\mathcal S\), commutes with the first
full (G)-chart.  Then

\[
 \rho_X(s_{11})=I.                                    \tag{UM3}
\]

This statement is independent of the dimension, composition factors,
semisimplicity, and indecomposable structure of (W).  It also applies
blockwise to arbitrary direct sums and arbitrary off-diagonal couplings.
Consequently, no square-zero construction over \(\mathbb F_2\) at the inner
order-zero alignment can retain the marked central phase.

## Reduction to one group-algebra identity

For an aligned boundary word (w=y_1\cdots y_m), let (p_tin G) be its
order-zero prefix through (y_t), with (p_0=p_m=1).  Define

\[
 d_w=\sum_{t:\,y_t\text{ lies in chart }2}(p_{t-1}+p_t)
       \in\mathbb F_2[G].                              \tag{UM4}
\]

The group algebra acts on \(\operatorname{End}(W)\) by conjugation:

\[
 g\cdot T=\sigma(g)T\sigma(g)^{-1}.
\]

Direct differentiation of `(UM1)` gives the universal formula

\[
 \rho_X(w)=I+\varepsilon(d_w\cdot X).                  \tag{UM5}
\]

Thus `(UM2)` says \(d_z\cdot X=0\) for every
\(z\in\mathcal Z_5\).  If (S) is the six-transvection generating set used
by the atlas, centrality of a survivor (s) says

\[
 (g+1)d_s\cdot X=0\qquad(g\in S).                     \tag{UM6}
\]

The exact computation certifies the following identity of left ideals:

\[
 d_{s_{11}}\in
 \sum_{z\in\mathcal Z_5}\mathbb F_2[G]d_z
 +\sum_{s\in\mathcal S}\sum_{g\in S}
      \mathbb F_2[G](g+1)d_s.                         \tag{UM7}
\]

Applying `(UM7)` to (X), then using `(UM2)` and `(UM6)`, proves
\(d_{s_{11}}\cdot X=0\).  Equation `(UM5)` is exactly `(UM3)`.

## Exact certificate

The verifier enumerates all 20,160 elements of (GL_4(2)), constructs the
28 derivative elements in `(UM4)`, and independently checks the group-algebra
formula for (d_{s_{11}}) against the direct (4\times4) natural-module
Jacobian.  There are 48 ideal generators: 24 zero derivatives and
\(4\cdot6\) centrality derivatives.

The archived derivation is a forward DAG.  Each of its 552 basis operations
is either an original ideal generator or a left translate of an earlier
row, followed by XOR reduction against earlier rows.  Twelve certified basis
rows XOR with (d_{s_{11}}) to zero.  The verifier reconstructs every row,
checks all pivots and backward references, and replays the final reduction.

```text
PYTHONPATH=experiments \
python3 experiments/atlas_universal_modular_group_algebra.py \
  --verify-certificate \
  experiments/atlas-universal-modular-group-algebra-certificate.json
```

Archived SHA-256 hashes:

```text
8df3ba10446d5386106d642473f77bbae7d3c12f03177a526844e50ab8bda1cc
  experiments/atlas-universal-modular-group-algebra.json
519b0ba8199c783b441f9cfc41753163305e771a880a8644e2e8f9349b29dc12
  experiments/atlas-universal-modular-group-algebra-certificate.json
```

## Scope and next construction boundary

This section records the direct characteristic-two certificate. The signed
identity has since been proved over **every field** in
`FALSE_ATLAS_FIRST_ORDER_GROUP_ALGEBRA_PRINCIPLE.md`, using this certificate
at (p=2), direct regular-algebra certificates at
(p=3,5,7,11,13,1181), and rational certificates for every remaining prime.
None of these results is a unitary local-rigidity theorem, excludes nonlinear
finite/tracial atlases with different order-zero holonomy, or by itself
proves or disproves hyperlinearity of the Leavitt witness.

The previous strategy “find a new indecomposable \(\mathbb F_2[A_8]\)-module”
is now closed: `(UM7)` is functorial over **all** such modules.  A surviving
FALSE construction must instead change at least one of:

1. genuinely nonlinear or higher-order deformation geometry;
2. the square-zero order;
3. the inner order-zero chart alignment; or
4. the use of one common (A_8)-module for the two full charts.

The higher-order theorem remains independently useful: in the natural
module, even changing coefficient field and raising the univariate
dual-number order cannot evade the obstruction. See
`FALSE_ATLAS_NATURAL_ALL_FIELD_HIGHER_ORDER_NO_GO.md`.
