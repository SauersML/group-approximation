# Audit: upper-semicontinuous AF-fibre fields

Date: 2026-08-30

Claim: `stw81-af-fibre-fields-have-base-bound`.

## Stress tests

1. **Neighborhood ideals.**  The equality
   `I_x=closure(union_k C_0(X minus K_k)A)` is proved on the defining
   generators `fa` of the fibre ideal.  It uses continuity of the scalar
   coefficient `f`, not continuity of the field.

2. **Nonunital fibres.**  A finite-dimensional subalgebra `E subset A_x`
   has its own unit `p`.  Compression to `pA_xp`, followed by injectivity of
   the finite-dimensional operator system `E`, gives a c.p.c. retraction.
   No unit in `A_x` is used.  The zero fibre is handled by `E=0`.

3. **Semiprojectivity.**  It is applied to the honest star-homomorphism
   `E -> A/I_x` and the increasing ideals `J_k`; the output is an exact
   star-homomorphism `E -> A/J_k`.  No approximate lift or local
   trivialization is asserted.

4. **Norm control.**  For an element of the restricted `C_0(K_k)`-algebra,
   `y -> ||b_y||` is upper semicontinuous.  Since the desired inequality is
   strict at the anchor, its strict sublevel set is an open neighborhood.
   Continuity is unnecessary.

5. **Localization.**  Multiplication by a central cutoff `g` is c.p.c. and
   annihilates `C_0(X minus K_k)A` when `supp(g) subset K_k`, so it factors
   c.p.c. through `A/J_k`.  Composing with the neighborhood homomorphism is
   order zero because products of lifts of orthogonal elements lie in
   `J_k` and are killed by `g^2`.

6. **Nonunital contractivity.**  If `p_i` is the image of the unit of the
   finite-dimensional block, a positive contractive lift `e_i` gives
   `g_i e_i<=g_i` in `M(A)`.  Hence the total return map has
   `phi(1)<=sum_i g_i=h<=1`; no fibre or quotient unit is assumed.

7. **Colouring.**  The finite cover is replaced by an
   `(n+1)`-decomposable refinement with disjoint closed supports within each
   colour.  Cross terms therefore vanish exactly, while the scalar weights
   still sum to `h`.

8. **Global norm.**  The approximation estimate is checked in every fibre
   and then promoted using `||a||=sup_x ||a_x||`, valid for arbitrary
   `C_0(X)`-algebras.

9. **Shadow-free simple fibres.**  Fibres of an arbitrary quotient are
   quotients of the original fibres, hence are zero or unchanged when the
   original fibres are simple.  The quotient image of `Her(c)` is
   `Her(c_x)`.  A nonzero commutative hereditary image would be full in the
   simple fibre and make that fibre Morita equivalent to a commutative
   algebra, which is exactly the excluded elementary case.  This argument
   uses neither continuity of fibre norms nor a homeomorphism
   `Prim(A)->X`.

## Scope and caveats

For arbitrary nonsimple fibres the theorem proves only the nuclear-dimension
bound and does not imply the separate “no commutative hereditary shadow”
hypothesis in Problem LXXXI.  Finite covering dimension, second countability,
local compactness, and separability are retained.  The dimension proof uses
no continuous-field, unitality, simplicity, local-triviality, or
constant-fibre assumption.

Outcome: **PASS**, with the continuity and unitality assumptions removed and
the shadow statement retained for simple non-elementary fibres.
