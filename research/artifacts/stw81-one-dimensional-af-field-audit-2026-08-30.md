# Audit: one-dimensional locally trivial simple AF fields

Date: 2026-08-30

Claim audited:
`stw81-one-dim-simple-af-fields-have-dim-one`.

## Checks

1. **No hidden third colour.** The fibre approximation uses a
   finite-dimensional subalgebra of the AF fibre and a c.p.c. retraction onto
   it; the return map is the inclusion multiplied by a scalar partition
   function, hence order zero. The only colours are the two base-cover
   colours.

2. **Local return maps glue.** Each partition function has support compactly
   contained in a trivializing patch, so the locally constant fibre section
   multiplied by that function extends continuously by zero.

3. **Sums remain order zero.** Within either colour the partition-function
   supports are disjoint. Products of outputs from distinct summands vanish,
   while each individual return map is order zero.

4. **Noncompact bases.** Compact localization by a central function in
   (C_c(X)) reduces every finite approximation problem to finitely many
   trivializing patches.

5. **All ideal quotients are covered.** Simplicity of the fibre identifies
   the primitive spectrum with the base. Ideals therefore correspond to open
   subsets, and quotients are restrictions to closed subsets with the same
   fibre.

6. **The hereditary contradiction is valid.** For a nonzero positive
   (c) in the commutative hereditary algebra, evaluation maps
   \(\overline{cBc}\) onto \(\overline{c(x)Dc(x)}\). The latter is a nonzero
   hereditary subalgebra of the simple fibre and therefore full. A simple
   algebra Morita equivalent to a commutative algebra is elementary,
   contradicting an infinite-dimensional unital simple AF fibre.

7. **It is genuinely outside the earlier fibre theorem.** Infinite-dimensional
   unital simple AF algebras are neither elementary nor purely infinite, so
   the locally trivial UHF case is not contained in the elementary/
   (mathcal O_\infty)-fibre node.

## Outcome

The proof is internally complete modulo standard definitions and the
standard coloured-refinement characterization of covering dimension. The
claim is ready for an independent audit.
