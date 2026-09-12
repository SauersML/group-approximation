---
rg: 2
id: equal-difference-four-word-and-amenable-chart-proof
kind: route
title: Compute the four-word Gram defect and lift one amenable Fourier chart
target: equal-difference-gram-averaging-fails-at-four-free-words
requires:
  - fourier-local-sections-already-descend-amenable-trace
  - leavitt-unit-internal-free-reflections
---

For an amenable subgroup `H<=G`, the reduced group algebra `C^*_r(H)` is
nuclear and embeds canonically in `C^*_r(G)`.  Choi--Effros lifts this
embedding through any unital quotient `q:A->C^*_r(G)`.  Concretely, take the
completely positive contractive lift `s_0`.  Since `q(s_0(1))=1`, the positive
defect `d=1-s_0(1)` lies in `ker(q)`; for any state `omega` on `C^*_r(H)`,
`s(x)=s_0(x)+omega(x)d` is a unital completely positive lift.  When `H` is finite,
the explicit formula `(EDA1)` proves the same assertion: equation `(EDA2)`
is a convex combination of positive Gram matrices, and the quotient of each
summand at difference `k` is `lambda_k`.

For the negative statement, reduced-word comparison in `F(a,b)` shows that
the four labels in `(EDA3)` have only the displayed off-diagonal collision
and its inverse.  Applying collision-class averaging to `(EDA4)` therefore
changes exactly the four positions `(1,2),(2,1),(3,4),(4,3)`, from
`1,1,-1,-1` to zero, and gives `(EDA5)`.  Direct multiplication by
`x=(1,1,-1,1)^T` gives `(EDA6)`.  Thus the arithmetic collision projection
is not positive.  The internal free-prefix result embeds these labels in the
binary Leavitt unit group.

Finally, a global positive projection onto equal-difference matrices is a
conditional expectation from `B(ell^2(G))` onto the left or right group von
Neumann algebra.  Such an expectation is injectivity of that von Neumann
algebra; for discrete `G`, injectivity is equivalent to amenability.  This
proves the stated global fence for the nonamenable Leavitt group.
