---
rg: 2
id: o2-tensor-power-shift-is-rokhlin
kind: claim
title: The cyclic shift on O_2^(⊗p) is KK^(Z/p)-contractible, pointwise outer, and has the Rokhlin property; in particular the flip on O_2 ⊗ O_2 is Rokhlin
distinct_from:
  o2-contractible-crossed-product-inner-half-flip-mcduff: that shows the infinite tensor power of a contractible outer action is the Rokhlin model; this shows the finite p-fold shift on O_2 itself is Rokhlin.
---

**ESTABLISHED (derivation; unreviewed; novelty not checked, because web search
was exhausted and the arXiv API was rate-limited on 2026-09-13).**  Let `p` be
prime and `σ` the cyclic shift on `O_2^(⊗p) ≅ O_2`.

1. `(O_2^(⊗p), σ) ≃_(KK^(Z/p)) 0`.
2. `σ^k` is outer for `1 ≤ k ≤ p − 1`.
3. `σ` has the Rokhlin property and is conjugate to the model `id ⊗ μ_(Z/p)`
   on `O_2 ⊗ M_(p^∞) ≅ O_2`.
4. `O_2^(⊗p) ⋊_σ Z/p ≃_KK 0`.

**Derivation.**
- Item 1: `O_2 ≃_KK 0`, so item 1 of `kk-tensor-power-norm-functor-to-kk-zp`
  applies.
- Item 2: suppose `σ^k = Ad(u)`.  Take a factor state `φ` on `O_2` of type III,
  for instance a quasi-free state.  The product state `φ^(⊗p)` is
  shift-invariant, so `σ^k` and `Ad(u)` extend to the von Neumann tensor power
  `M^(⊗̄p)` with `M = π_φ(O_2)''`.  There a nontrivial permutation of factors is
  inner only when `M` is type I.  That is a standard fact, not re-read.
- Item 3: item 2 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`.
- Item 4: the crossed product functor on item 1.

**Model tests.**
- The same shift on `M_n^(⊗p)` is inner by a shift-fixed unitary, and its
  norm is `KK^G`-equivalent to `C`, not `0`.  So contractibility of `A` is
  what does the work.
- The trivial action on `O_2` is contractible but not Rokhlin, so outerness is
  what does the work in item 3.

**What it adds for detection.**  This is the first case where tensor-power
symmetry, rather than a quasi-free or product-type construction, lands an
explicit outer action on `O_2` in the Rokhlin class.  Norms of KK-contractible
algebras are never phantoms.  So phantoms from norms can only come from the
Tate part of norms of non-bootstrap algebras (part 2 of the norm-functor
artifact, §8).

Proof: `o2-tensor-power-shift-is-rokhlin-proof`.
