# Coordinate twists do not enlarge the atlas swap symmetry

Date: 2026-08-11

Let

\[
 C_1=(01,1,000,001),\qquad C_2=(00,1,010,011)
\]

be the two scalar leaf charts in the binary Leavitt atlas, and write
\(K_i\cong GL_4(\mathbf F _2)\) for their unit groups.  The known prefix
replacement \(v\) exchanges the charts while preserving matrix coordinates:

\[
 vK_1v^{-1}=K_2,\qquad vK_2v^{-1}=K_1.             \tag{1}
\]

This note closes the most immediate enlargement of that symmetry.

## 1. All coordinate-twisted swaps

Any twist on either side of \(v\) reduces to

\[
 w_M=M_2v,\qquad M\in GL_4(\mathbf F _2),           \tag{2}
\]

because \(vN_1v^{-1}=N_2\).  Equation `(1)` gives

\[
 w_MK_1w_M^{-1}=K_2,
 \qquad
 w_MK_2w_M^{-1}=M_2K_1M_2^{-1}.                    \tag{3}
\]

Consequently \(w_M\) exchanges the two chart subgroups if and only if

\[
 M_2\in K_2\cap N_Q(K_1),
 \qquad Q=L_{\mathbf F _2}(1,2)^\times.             \tag{4}
\]

## 2. Exact normalizer exhaustion

`experiments/atlas_twisted_swap_normalizer.py` enumerates all 20,160
matrices in \(GL_4(\mathbf F _2)\).  For each \(M\), it conjugates the six
standard transvection generators of \(K_1\) by the Leavitt unit \(M_2\),
then tests exact membership in the scalar chart \(C_1\).  Membership is
decided by expanding the Leavitt monomials and the sixteen matrix units of
the chart to common right depths and applying Gaussian elimination over
\(\mathbf F _2\).  Thus no floating-point or bounded prefix comparison is
used.

The output is

```text
chart_group_order                 20160
normalizer_intersection_order         1
normalizer_elements              {I_4}
```

Testing generators is sufficient: if all six conjugates lie in \(K_1\),
then \(M_2K_1M_2^{-1}\leq K_1\); both finite groups have order 20,160, so
equality follows.  We have therefore proved

\[
 K_2\cap N_Q(K_1)=\{1\}.                             \tag{5}
\]

## 3. Consequence for the surviving central classes

The only coordinate-twisted chart exchange is the original \(v\).  Its
exact action on the four conjugacy/inversion classes is

\[
 11\leftrightarrow55,
 \qquad
 30\leftrightarrow44,                               \tag{6}
\]

with positive orientation.  Hence this entire family supplies exactly the
two already known equalities in \(R/[P,R]\), and gives neither
\([r_{11}]=\pm[r_{30}]\) nor a self-inverse relation for either remaining
class.

The scope is important.  Equation `(5)` exhausts every two-sided
**coordinate twist of the explicit prefix swap**.  It does not compute the
full normalizer of either chart in \(Q\), rule out an unrelated Leavitt
inner automorphism, or decide whether the two central classes vanish by a
genuinely non-scalar multi-chart relation.  Those remain the live algebraic
possibilities.
