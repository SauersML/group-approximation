---
rg: 2
id: crossed-product-gl-n-has-infinite-cyclic-index-quotient
kind: claim
title: The half-orbit Fredholm index maps GL_n(LC(X,k) ⋊ Z) onto Z and vanishes on EL_n, so GL_n is neither simple nor Kazhdan
distinct_from:
  binary-jacobson-elementary-symbols-have-zero-toeplitz-index: that is a Toeplitz index for the binary Jacobson head ring; this is the half-orbit index on every crossed product of a zero-dimensional system by Z, used to show that the note's group must be EL_n and not GL_n.
---

**ESTABLISHED (unreviewed)** by `crossed-product-gl-n-has-infinite-cyclic-index-quotient-proof`.

**Statement.** Let `X` be a nonempty compact metrizable zero-dimensional space, `T` a homeomorphism, `k` a field, `R = LC(X,k) ⋊_T Z`, and `n ≥ 1`. Then there is a group homomorphism `ind: GL_n(R) → Z` with:
- `ind(e_ij(r)) = 0` for every elementary matrix, so `EL_n(R) ⊆ ker(ind)`;
- `ind(diag(u,1,…,1)) = −1`, so `ind` is surjective.

So `GL_n(R)` has `Z` as a quotient. It has no property (T). For `n ≥ 2` it is not simple, since `EL_n(R)` is a nontrivial subgroup of the proper normal subgroup `ker(ind)`.
If `X` is minimal, then `Z(GL_n(R)) = k^× I_n` lies in `ker(ind)`, so `GL_n(R)/Z` is not simple either.

**Use for the note:** the group of the theorem has to be the elementary group. Replacing `EL_3` by `GL_3` destroys both simplicity and property (T), for every subshift `X`.
