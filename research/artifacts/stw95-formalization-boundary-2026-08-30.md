# Problem XCV counterexample: theorem and formalization boundary

Date: 2026-08-30.

## Unconditional statement

There is a separable unital simple nuclear UCT and Jiang--Su-stable C*-algebra
`E` such that

```text
Cu(E) isomorphic to Cu(Z),
Cu(E tensor_min E) not isomorphic to Cu(Z).
```

One concrete choice is

```text
E = (tensor_(j in Z) Z) crossed_product_shift Z.
```

The abstract range-theorem construction with ordered `K_0=(Z,N_0,1)`,
`K_1=Z`, and one trace is an independent choice with the same proof.

## Exact theorem chain

The following operator-algebra results are imported into the paper proof.
They are the complete current non-kernel trust boundary.

1. Countable tensorial absorption identifies `tensor_(j in Z) Z` with `Z`.
   Strong outerness itself has a direct finite-support/`L^2` proof, recorded
   in `stw95-bernoulli-z-crossed-product-counterexample-proof`.
2. Simplicity (pointwise outer crossed products), nuclearity (amenable crossed
   products), and UCT permanence under crossed products by `Z` are separate
   imported results.  Monotraciality has a direct Fourier-coefficient proof
   from strong outerness.  Z-stability imports Matui--Sato Corollary 4.11 and
   Remark 4.12; all their hypotheses are checked in the route.  Equivalently,
   the abstract route imports the range theorem for the displayed Elliott
   invariant.
3. The Pimsner--Voiculescu sequence computes `K_0(E)=Z`, `K_1(E)=Z`; the UCT
   Kunneth sequence computes `K_0(E tensor_min E)=Z^2`.
4. A simple finite Z-stable algebra has stable rank one.
5. For a simple unital stably finite pure algebra,
   `Cu(A)=V(A) disjoint_union LAff(QT(A))_(strictly positive)`.
6. For stable rank one, compact Cuntz elements are exactly projection
   classes; their Grothendieck group is `K_0`.
7. A Cu-isomorphism preserves the way-below relation, hence its compact
   submonoid.

Items 1--6 are not available as Mathlib definitions or theorems: Mathlib has
neither the Cuntz semigroup nor operator K-theory.  They were therefore **not**
introduced as Lean axioms or hypotheses.

## Kernel-checked endpoint

`GroupApproximation/Manuscript/NinetyNineProblems/ProblemXCVCompactKTheory.lean`
proves the terminal contradiction

```text
not Nonempty (Z is_additively_isomorphic_to (Z times Z)).
```

The proof is elementary and unconditional: an additive equivalence is
determined by the image `(a,b)` of `1`; surjectivity onto `(1,0)` forces
`b=0`, contradicting surjectivity onto `(0,1)`.  The module imports no project
theorem and declares no axiom, `sorry`, `admit`, or placeholder.

A full unconditional Lean formalization remains **incomplete**.  It requires
implementing the missing crossed-product, operator `K`-theory, stable-rank and
Cuntz-semigroup foundations, not merely filling a local lemma.  The present
module formalizes only the terminal arithmetic implication available in the
current library.  It is not, and must not be described as, a formalization of
the operator-algebra counterexample itself.
