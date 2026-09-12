---
rg: 2
id: kt-kazhdan-edge-grams-are-conditioned-only-at-fixed-radius
kind: claim
title: Kazhdan edge-word Grams are conditioned only on fixed windows
distinct_from:
  kt-edge-expectation-is-a-moving-coset-gram-supremum: That shows pointwise canonical characters do not control a moving conditional-expectation witness; this gives an explicit exact canonical vertex sequence whose moving edge-word basis has arbitrarily small least Gram eigenvalue.
  kt-return-expectation-pays-one-full-edge-principal-angle: That bounds the return expectation by covariance leakage divided by word-basis conditioning; this proves property (T) cannot supply the missing moving conditioning in that bound.
  commutant-density-trace-blind: That computes a normalized commutant dimension and shows it vanishes on regular-character models; this concerns conditioning of finite edge-word Gram matrices and its failure at moving radius.
---

Let `Gamma<G` be the residually finite Kun--Thom pair.  Property `(T)` of
`Gamma` gives no uniform lower bound on the least Gram eigenvalue of a
moving edge-word basis, even for exact finite-dimensional representations
of `G` with canonical limiting character.

There are two complementary precise statements.

1. **Fixed windows are automatically conditioned.**  If `F subset Gamma`
   is a fixed finite set of distinct elements and `chi_n` is any sequence of
   characters with

   ```text
   chi_n(g)->delta_(g,1),
   ```

   then the Gram matrix

   ```text
   G_(n,F)(x,y)=chi_n(x^(-1)y)                           (KGC1)
   ```

   converges to the identity.  Quantitatively, if every off-diagonal entry
   has modulus at most `epsilon`, then

   ```text
   lambda_min(G_(n,F))>=1-(|F|-1)epsilon.               (KGC2)
   ```

   This uses no Kazhdan gap.

2. **Moving windows can be arbitrarily ill-conditioned.**  Given any
   positive sequence `a_n->0`, there are exact finite-dimensional
   representations

   ```text
   rho_n:G->U(d_n)
   ```

   with canonical limiting character and nontrivial elements
   `k_n in Gamma` such that `1,rho_n(k_n)` are linearly independent but

   ```text
   lambda_min Gram(1,rho_n(k_n))<=a_n.                  (KGC3)
   ```

   The pair can be extended to a basis of `C*(rho_n(Gamma))` consisting of
   group-image words, and the least eigenvalue of the full basis Gram is
   still at most `a_n`.

Consequently no use of property `(T)` or of the canonical vertex character
can remove the `lambda_n^(-1)` escape in `(KPA10)` of
`kt-return-expectation-pays-one-full-edge-principal-angle`.  Any conditioning
argument sufficient for Certificate C must use additional compatibility
with the approximate compressor action at a moving word radius; bounded
Kazhdan windows alone cannot provide it.

DERIVATION
kt-moving-edge-gram-degeneration-proof
