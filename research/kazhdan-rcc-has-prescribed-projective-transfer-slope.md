---
rg: 2
id: kazhdan-rcc-has-prescribed-projective-transfer-slope
kind: claim
title: Canonical RCC has ordinary and projective transfer with the prescribed Kazhdan coefficient and no perfectness hypothesis
distinct_from:
  rf-perfect-pair-transfer-equals-regular-rcc: that assumes residual finiteness and perfectness and obtains an unspecified linear coefficient by tensor amplification; this only assumes hyperlinearity and a Kazhdan subgroup, removes perfectness, and prescribes the coefficient 4/kappa^2 with a qualitative defect modulus.
  exact-projective-codensity-has-a-uniform-trace-square-gap: that treats exact finite-dimensional actors and cancels phases using perfectness; this treats arbitrary approximate actors and uses inner superoperator matrices instead of phase cancellation.
  projective-transfer-linear-bound-equals-no-ultraproduct-leak: that amplifies small target energies to obtain some linear presentation-defect bound; this preserves a specified Kazhdan coefficient with a qualitative modulus and obtains a linear defect term at every strictly larger coefficient.
artifacts:
  - research/artifacts/prescribed-kazhdan-rcc-transfer-audit-2026-09-07.md
---

Let A=<X|R> be finitely presented and hyperlinear, let C=<S><=A have
property (T), and fix h in A with A=<C,h>. Choose words in X for S and h.
Let kappa>0 be a Kazhdan constant for S, in the convention

    max_(s in S)||beta(s)xi-xi|| >= kappa||xi||

on the orthogonal complement of invariant vectors in every unitary
representation beta of C. Put K=4/kappa^2.

For a unitary assignment rho:X->U(d), evaluate all words multiplicatively
and set delta(rho)=max({0} union {||rho(r)-I||_2:r in R}). All traces and
Hilbert--Schmidt norms below are normalized.

The following four assertions are equivalent.

1. For every tracial matrix ultraproduct M and every canonical-trace
   representation pi:A->U(M),

       pi(C)' cap M = pi(A)' cap M.                      (KRT1)

   Canonical means tau(pi(a))=0 for every a!=1 in A.

2. There is a nonnegative nondecreasing function eta_o on [0,infinity),
   with eta_o(0)=0 and eta_o(delta)->0 as delta->0, such that every d,
   every assignment rho:X->U(d), and every contraction x in M_d satisfy

       ||x rho(h)-rho(h)x||_2^2
        <= K sum_(s in S)||x rho(s)-rho(s)x||_2^2
              +eta_o(delta(rho)).                       (KRT2)

3. There is such a function eta_p for which every d, every assignment
   rho, and every unitary U in U(d) satisfy, with
   W_a=U rho(a) U^* rho(a)^*,

       1-|tr(W_h)|^2
       <= K sum_(s in S)(1-|tr(W_s)|^2)
              +eta_p(delta(rho)).                       (KRT3)

4. For every K'>K there is a finite L_(K')>=0 such that every d, every
   assignment rho, and every unitary U satisfy

       1-|tr(W_h)|^2
        <= K' sum_(s in S)(1-|tr(W_s)|^2)
              +L_(K') delta(rho).                       (KRT4)

   This inequality holds for all assignments, without an additional
   small-defect hypothesis. Its defect term is linear in the ordinary,
   unsquared defining-relator defect delta(rho).

In the implication from (KRT2) to (KRT3), one may take

    eta_p(delta)=eta_o(2delta)/2.                         (KRT5)

Given this nondecreasing eta_p, an explicit sufficient choice in (KRT4)
is any L_(K')>=1 such that

    eta_p(1/L_(K')) < ((1-K/K')/2)^2.                    (KRT6)

Such a finite choice exists because eta_p tends to zero. The choice is
in terms of that modulus and is not claimed computable from the group
presentation alone.

Neither A nor C is assumed perfect or residually finite. Hyperlinearity
of A regularizes arbitrary actor traces by tensoring with the canonical
representation of A. The Kazhdan projection then gives the exact
coefficient K in every Connes-embeddable ambient algebra. Compactness
supplies the defect modulus while retaining that coefficient.

The contraction restriction in (KRT2) is essential for a uniform additive
modulus; unrestricted scaling of x is not covered. No effective modulus
or uniform linear bound eta_o(delta)<=L delta is asserted here. In
particular, a projective linear-defect bound at the EXACT coefficient K
remains unclaimed; (KRT4) allows every strictly larger coefficient.

Projective transfer implies actual commutation without a perfectness
argument because its quantifiers permit replacing rho by rho direct_sum
rho and U by U direct_sum I. This is a global equivalence across all
matrix sizes and embeddings, not an assertion about scalar removal in
one fixed representation.

For SL_n(Z)<=SL_n(Z[1/p]), n>=3, the theorem gives a concrete prescribed
slope for the transfer target. It does not prove that this arithmetic
pair satisfies any of the equivalent assertions.
