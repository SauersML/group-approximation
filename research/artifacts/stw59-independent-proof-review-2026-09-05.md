# Independent review of the simple AH counterexample

The complete argument is in
[the manuscript](stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md).
Two independent internal mathematical readings found no unresolved gap
in the finite obstruction or its persistence in the simple limit. This
record describes what was checked. It is not external peer review,
publication acceptance, or formal verification.

## The obstruction includes every possible cancellation

An isomorphism between the two complementary bundles extends, by polar
decomposition and the prescribed map of their trivial line summands, to
an actual unitary automorphism of the ambient bundle. The associated
mapping torus therefore includes every possible isomorphism, without
assuming that stable gauge classes are realized by actual automorphisms.

The displayed interpolation has exactly one zero in its sphere and
interval coordinates. Its derivative is a real-linear isomorphism.
Multiplying this zero count by the top Chern number of the sum of
tautological line bundles gives an odd Euler number. The section is
nonvanishing near the gluing seam, so smoothing there does not alter
the local indices.

Independently, the restriction kernel in the mapping-torus K-group is
the odd sphere generator times the projective-space K-group. The odd
Chern character has coefficient one. Hatcher's Proposition 4.3 gives
the integral normalization after suspension. The coefficient in degree
\(2q\), for a multi-index \(b\) of weight \(q-3\), is

\[
\pm (|b|+2)(|b|+1)
\binom{|b|}{b_1,\ldots,b_\ell}\prod_j a_j^{b_j}.
\]

It is even for every integral line monomial. Since all the relevant
integral cohomology groups are torsion-free, this proves integral
divisibility, not just a rational identity. Multiplication by the
ambient bundle's integral Chern classes preserves parity. Thus every
possible mapping torus has even top Chern number, contradicting the
explicit odd zero count.

## The inductive limit satisfies the question's hypotheses

The connecting homomorphisms act on the actual direct-sum bundles;
their point-evaluation terms tensor a fixed finite-dimensional fiber
with a line bundle. They are globally defined, unital and injective.
The coordinate summand retains a nonzero stage positive element at
a suitable evaluation point. Its next evaluation block is then
nonzero at every fiber, making that stage image full.

The manuscript's positive cutdown argument shows that every nonzero
limit ideal contains such a nonzero stage element. This proves
simplicity, rather than merely separation of finite-stage points.
The trace inverse-limit argument does not assume surjectivity of trace
restriction maps. Simplicity makes the resulting trace faithful and
therefore proves stable finiteness.

At each stage the distinguished unitary is homotopic to the canonical
sphere unitary plus the identity on the twisted complement. Contracting
a point-evaluation matrix tensored with the same line bundle is valid
globally. The finite obstruction applies to exactly this complement.
Finally, the explicit polar-decomposition and logarithm estimates show
that a limit null-homotopy would occur at a later finite stage. This
closes the persistence step.

The original sphere class has order two. A single matrix amplification
supplies a trivial stabilizing line and kills it, while the unamplified
limit class survives. Separately, even-cell K-theory and continuity
give \(K_1(A)=0\). No assertion that the whole component group is
\(\mathbb Z/2\) is needed or made.

## Existing theorems and the exact conclusion

Seth's Definition 2.1 explicitly uses full-matrix building blocks over
spaces and scalar diagonal eigenvalue maps. The twisted endomorphism
bundle system does not satisfy that presentation hypothesis. The
manuscript therefore does not contradict the published diagonal AH
K-stability theorem by misapplying its definition.

The result addresses the universal assertion in STW Problem LIX.
It does not answer the different properly infinite question, the
pure-algebra K-stability problem, or all the other STW problems.
The problem list and the relevant diagonal theorem were checked
against their available primary manuscripts on 5 September 2026.
No claim of exhaustive publication novelty is established by this
review.

## Cairn integration check

The exact six-node dependency closure passed `cairn check --changed`
and `cairn preview` on MSI with Python 3.11: four claims and two routes.
The counterexample and historical finite test derive `ESTABLISHED`;
the universal assertion in STW LIX changes from `OPEN` to `REFUTED`.
Full-snapshot duplicate checking found no unresolved duplicates for
the two new claims.

The initial imported full graph had 37 unrelated source errors. A
subsequent full-source audit on the same date passed with 14,104 nodes,
zero findings, and zero duplicate candidates; its exact snapshot and
checks are recorded in
[the later review](stw99-lxxvi-all-base-review-2026-09-05.md).
The original LIX scoped logs are
in `stw79-cairn-check-20260904/stw59-full-proof-scope-20260905` under
the shared MSI project directory. The adjacent
`stw59-full-proof-global-audit-20260905.json` records the global audit.
Cairn checks the graph and its declared derivations; the mathematical
review described above is separate from that structural check.
