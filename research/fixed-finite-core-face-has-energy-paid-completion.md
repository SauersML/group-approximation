---
rg: 2
id: fixed-finite-core-face-has-energy-paid-completion
kind: claim
title: Every fixed finite core face has an energy-paid exact completion
distinct_from:
  fixed-level-bs14-compatible-basin: that gives flexible stability of each entire finite quotient and isolates the moving basin-radius comparison; this gives a direct core-face dichotomy and an explicit regular-representation completion when the face has no exact extension.
  a5-d10-parity-blocks-have-energy-paid-repair: that computes the efficient one-line completion of one concrete parity face; this proves existence for every fixed finite quotient/core face, generally with nonuniform and inefficient padding.
  congruence-induction-cannot-reconstruct-a-low-rank-bs14-boundary: that shows regular/induced completion is quantitatively unusable as the level moves; this uses it only at one fixed level and exposes the exact level-dependent constant.
---

**ESTABLISHED FIXED-FACE THEOREM.**  Let `Gamma` be the fixed finitely
presented Iwahori group, let `q:Gamma->G` be a fixed finite quotient, and let
`H=q(B)` be the image of its BS core.  Fix a finite-dimensional unitary
representation `sigma` of `H`, realized as an exact BS core on `C^d`.  Let
`E_sigma(X)` be the unnormalized sum of squared Frobenius defects of the
remaining Iwahori relators for `X in U(d)`.

There are a fixed integer `k_sigma>=0`, a constant `C_sigma<infinity`, and
a same-core correction modulus on the extendible branch, with the following
dichotomy.

1. If some exact Iwahori representation has core `sigma`, then the zero set

   ```text
   Z_sigma={X:E_sigma(X)=0}                            (FFC1)
   ```

   is nonempty and compactness gives

   ```text
   dist(X,Z_sigma)<=f_sigma(E_sigma(X)),
   f_sigma(t)->0.                                     (FFC2)
   ```

   Here `k_sigma=0`.
2. If `(FFC1)` is empty, then

   ```text
   delta_sigma=min_(X in U(d)) E_sigma(X)>0.           (FFC3)
   ```

   Choose `M` so that `sigma` is a subrepresentation of

   ```text
   res_H^G(M lambda_G)=M[G:H] lambda_H.                (FFC4)
   ```

   Let `tau` be its orthogonal complement and put `k_sigma=dim(tau)`.  The
   pulled-back exact representation `M lambda_G` is a joint Iwahori
   completion of `sigma (+) tau`, and

   ```text
   k_sigma<=C_sigma E_sigma(X),
   C_sigma=k_sigma/delta_sigma.                        (FFC5)
   ```

Thus block-diagonal sums of any **fixed finite list** of authenticated core
faces admit flexible repair with padding linear in unnormalized energy and
vanishing normalized-HS displacement.  Exact joint Gram compatibility is
automatic because the completion is an honest finite-quotient
representation.

The theorem also identifies the precise failure of pointwise compactness to
solve the moving-level problem.  For a family `(G_n,H_n,sigma_n)`, the
argument gives constants

```text
C_(sigma_n)=k_(sigma_n)/delta_(sigma_n),               (FFC6)
```

and supplies no bound on their supremum.  The regular completion in
`(FFC4)` can have dimension comparable to the quotient index, while the
energy floor can simultaneously shrink.  Hence a level-uniform theorem
requires a native efficient completion and a uniform energy charge; it
cannot be obtained by diagonalizing finite-dimensional compactness.

This is an exact finite reduction, not the desired moving theorem.  It does
not authenticate a block decomposition when the supplied `X` mixes core
types, and it deliberately records rather than hides all level dependence
in `(FFC6)`.

DERIVATION
fixed-finite-core-completion-proof
