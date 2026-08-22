# Universal-attack finite-witness audit — 2026-08-22

The supplied report's Sections 1--3 and 11--13 reduce to three assertions.

1. **Finite canonical witness for a nonhyperlinear countable group:** valid.
   The contrapositive diagonal construction is recorded in
   `nonhyperlinear-group-has-finite-canonical-microstate-witness`.
   The witness is non-effective and presupposes nonhyperlinearity; it does not
   construct a candidate group.
2. **Symmetry-basis input:** valid, with one citation correction.  The current
   arXiv:2605.15006v2 is He--Tang--Zhang, *The separable case of Kadison's
   problem on orthonormal bases of unitaries for type II_1 factors*, Theorem
   **1** (not Theorem 1.2).  It proves that every separable diffuse finite
   tracial von Neumann algebra has a complete `L^2`-orthonormal basis of
   self-adjoint unitaries.
3. **Finite non-CE symmetry witness:** valid after retaining trace moments.
   `non-ce-algebras-have-finite-symmetry-moment-witnesses` extracts finitely
   many basis symmetries, finitely many words and one uniform matrix gap.
   Common amplification preserves the obstruction exactly.

The last qualification is decisive.  The basis theorem is Hilbert-space
linear, not multiplicative.  If its symmetry basis were closed under products
up to phase, its projective index group would have exponent two and the
twisted group algebra would be hyperfinite.  Thus a non-CE basis necessarily
has products with spread coefficients.  A finite forbidden moment profile is
not an ordinary group presentation and is not the canonical delta character.

Accordingly the report's final synthesis is correct only as a reduction:
after finite witnessing and amplification invariance, the remaining theorem
is canonical trace promotion.  One must either place the non-CE algebra in a
positive group-factor corner, or decode its finite forbidden moment profile
from canonical microstates using a genuinely matrix-only transducer.  The
2026 symmetry-basis theorem supplies bounded involutive coordinates but
neither route by itself.
