---
rg: 2
id: truncated-polynomial-binary-weyl-expander-tower
kind: claim
title: Truncated binary polynomials carry a nested one-qubit Weyl tower with fixed relative-Kazhdan expanders
distinct_from:
  jacobi-congruence-clifford-tower: that asks for one finitely presented honest group realization compatible with the rank gate; this constructs the exact finite-level projective models and their abstract one-cell inclusions.
  explicit-constant-degree-quantum-expanders: that gives general circuit-explicit channels; these channels are evaluations of one fixed finite set of words over all truncation levels.
---

Put `R=F_2[u]`, `R_n=R/(u^n)`, and let `ell_n:R_n->F_2` extract the
coefficient of `u^(n-1)`. On `V_n=R_n^2` define

```text
omega_n((a,b),(c,d))=ell_n(ad+bc).                              (TPW1)
```

Then:

1. `omega_n` is a nondegenerate alternating `F_2`-form;
2. its Weyl representation on `H_n=l^2(R_n)` is projectively irreducible and
   has dimension `2^n`;
3. `EL_2(R_n)` preserves `omega_n`, hence the affine group
   `EL_2(R_n) semidirect V_n` has a projective Clifford--Weil representation
   extending the Weyl operators;
4. the maps

   ```text
   i_n:V_n -> V_(n+1),  (a,b) |-> (ua,b)                       (TPW2)
   ```

   are symplectic embeddings whose orthogonal complements are hyperbolic
   planes. Consequently their extraspecial groups and spin modules form an
   abstract nested tower adding exactly one Pauli qubit per step; and
5. there is one finite symmetric word set `S` and `lambda<1`, independent of
   `n`, such that the lazy adjoint channel of the images of `S` has
   normalized Hilbert--Schmidt norm at most `lambda` on traceless
   `End(H_n)`.

For item 5, take `S` from relative property `(T)` of
`EL_2(R) semidirect R^2` relative to `R^2`, pass to the quotient at level
`n`, and apply `relative-t-heisenberg-adjoint-quantum-expansion` to the
projective representation.

This is already the desired binary growth rate and uniform analytic gap.
It is not yet the finitely presented Clifford tape: the symplectic embeddings
`i_n` are not ring homomorphisms, the `EL_2(R_n)` actions need not preserve
their images, and the cocycle uses the level-dependent functional `ell_n`.
The level-dependent sign can be transported by conjugacy in a ring-valued
Heisenberg center, as explained by
`conjugate-local-signs-preserve-marked-carrier`. The genuine remaining issue
is to make that compressor coexist with the fixed expander implementers and
the one-cell inclusions in one finite presentation.
