# Problem LXXII: finite-ideal-lattice collapse audit (2026-08-30)

## Result

Weakly purely infinite C-star algebras with finitely many closed two-sided
ideals are purely infinite.  This is unconditional and allows incomparable
ideals, so it is not a restatement of the previously established chain-ideal
case.

## Proof audit

Take a maximal chain of ideals.  Consecutive subquotients are simple because
an ideal of a closed ideal is an ideal of the ambient C-star algebra.  Weak
pure infiniteness passes to ideals and quotients, hence every consecutive
simple subquotient is weakly purely infinite.  The established chain-ideal
theorem makes each such subquotient purely infinite.  Kirchberg--Rordam's
extension permanence for pure infiniteness then reconstructs the algebra one
composition step at a time.

The proof uses neither a primitive-spectrum separation hypothesis nor an
attempt to add square-zero elements from incomparable ideals.  Its new idea
is to move the gluing problem from nilpotents to exact extensions, where pure
infiniteness already has the required permanence.

## Literature boundary

The extension input is the permanence theorem in E. Kirchberg and M. Rordam,
*Non-simple purely infinite C-star algebras*, American Journal of Mathematics
122 (2000), 637--666, DOI `10.1353/ajm.2000.0021`.  The unrestricted
weak-to-pure implication remains open; this note claims only the finite ideal
lattice class.

