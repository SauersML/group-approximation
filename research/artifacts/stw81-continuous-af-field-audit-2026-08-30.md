# Audit: continuous AF-fibre fields without local triviality

Date: 2026-08-30

Claim: `stw81-continuous-simple-af-fields-have-base-bound`.

## Logical checks

1. The ideals `J_k=C_0(X minus K_k)A` increase to the fibre ideal. The only
   analytic input is continuity of the norm functions, which permits cutting
   off an element whose fibre at `x` vanishes.

2. Semiprojectivity is applied only to a finite-dimensional C-star algebra
   `E_x`, and only to the standard sequential quotient
   `A/closure(union J_k)`. It gives an exact star-homomorphic lift over one
   closed neighborhood, not a global trivialization.

3. The lifted model approximates the original sections throughout a smaller
   neighborhood because their difference is a section of a continuous
   quotient field. No identification of distinct fibres is used.

4. Multiplication by a cutoff supported in the interior of the closed
   neighborhood is independent of the chosen representative in `A/J_k`.
   Central multiplication of a star-homomorphism is order zero.

5. Equal-coloured support disjointness makes the sums order zero. The total
   return map is contractive because each lifted unit is a projection bounded
   by the multiplier unit and the scalar weights sum to `h<=1`.

6. Every simple fibre here is separable and hence primitive, while continuity
   makes `{x:a_x!=0}` open. Thus the
   structure map is a homeomorphism and all ideal quotients are field
   restrictions.

7. Evaluation of `closure(cBc)` is exactly
   `closure(c_x A_x c_x)`, avoiding any unsupported assertion that arbitrary
   homomorphic images of hereditary subalgebras are hereditary.

## Outcome

The argument removes local triviality and allows varying unital AF fibres.
An independent adversarial audit checked the localization map from `A/J_k`
back to `A`, its matrix-level complete positivity and order-zero property,
the decomposable-refinement step, and the primitive-spectrum argument. The
package passed; the proof now includes the two requested calculations
explicitly.
