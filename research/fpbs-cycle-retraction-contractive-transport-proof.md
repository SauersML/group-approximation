---
rg: 2
id: fpbs-cycle-retraction-contractive-transport-proof
kind: route
title: Charge added cycle dimension and use polar transport for connected deletions
target: fpbs-cycle-retraction-contractive-transport
requires:
  - fpbs-relative-cycle-operator-descent
  - fpbs-graphing-cost-betti-cycle-dimension-identity
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-iteration.md
---

Section 2 supplies the operator proof. The deleted-edge module is
boundedly isomorphic to ker R. On its orthogonal complement, R is
bijective onto the retained edge module and its inverse is a
contraction. Polar decomposition gives a unitary U and |R|>=I on
this restricted domain. Transporting the compression of K by U
preserves positivity and the upper bound by I, while its trace is
Tr(K)-Tr(P_W K) and is at most Tr(R K R-star).

For cycle-supported K, restrict the polar decomposition to
Z(H) intersect W-perp. Finite path replacements give W contained
in Z(H) and R Z(H)=Z(J), so the resulting contraction is supported
on Z(J). Dimension invariance and trace splitting give the exact
cost identity. Section 3 proves its iteration and initializes it
using the required relative-operator trace identity. The proof
does not invoke or assert the missing trace-decay estimate.

For additions, Section 5 uses the required dimension identity on
H and H^+, which generate the same relation. Their nested cycle
projections differ by a projection of trace c(H^+)-c(H)=a.
This new projection is orthogonal to the old cycle space, so adding
it to K preserves the positive-contraction bound and adds a to
the trace. The quantity c(H)-Tr(K) is unchanged. Combining this
step with the proved deletion identity gives the fully charged
nonmonotone iteration, without a claim of trace decay.

Section 8 proves spectral monotonicity directly. For a compression
B=P_V K P_V on V, the ranges of 1_[0,t](B) and 1_(t,1](K)
have zero intersection, by their contradictory quadratic-form
inequalities on a common nonzero vector. Finite-module dimension
then bounds the low-spectrum trace of B by that of K. Polar
unitaries preserve it; additions only append eigenvalue one.
The required cost--Betti dimension identity gives z(H_n)>=g,
and integration above t gives the stated trace lower bound.
Normality at t decreasing to zero supplies the kernel criterion.

Section 9 constructs the genuine zero-kernel examples. Countably
color the finite cycles into vertex-disjoint bounded-length
families; repeat each family for every possible deleted edge.
Each resulting J_j generates. The intersection of Z(J_j) is zero
because every edge in any finite cycle is deleted in at least one
J_j. Mixing these graphings, and H with positive mass, on invariant
copies of X yields K=epsilon sum p_j(P_H-P_Jj), with zero kernel
on Z(H). Componentwise restriction proves the extension still has
cost C(X). The finite-label approximation in the required relative
operator claim supplies near-optimal H for finitely generated
groups. This construction proves a limitation of the trace-zero
target; it does not prove a positive cost--Betti gap exists.

Section 10 obtains the signed stopping criterion by rearranging
the already proved ledger, retaining all accumulated eta terms.
