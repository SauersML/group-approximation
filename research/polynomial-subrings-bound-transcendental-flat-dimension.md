---
rg: 2
id: polynomial-subrings-bound-transcendental-flat-dimension
kind: claim
title: If a k-algebra A has n commuting algebraically independent elements, then A ⊗_k k(y_1, ..., y_n) has weak and left global dimension at least n, with no flatness of A over the polynomial subring
distinct_from:
  quasi-free-algebras-have-no-trdeg-two-subfields: that lower bound induces the diagonal Koszul resolution from a subfield F, and needs A to be free over F. This one uses only a polynomial subring C and needs no flatness of A over C, because the fraction field of C is flat over C.
  leavitt-algebras-have-no-trdeg-two-subfields: that is the Leavitt instance of the subfield version, whose text records that the polynomial version needs L to be flat over the commutative subring. This claim removes that hypothesis.
  finite-field-polynomial-growth-hosts-bound-commuting-rank: that bounds commuting rank by counting dimensions in growth-r^s operator algebras over finite fields. This is a field-independent homological lower bound.
---

**ESTABLISHED** by `polynomial-subring-flat-dimension-via-fraction-field-koszul` (unreviewed).

Let `k` be a field and `A` a nonzero `k`-algebra with unit. Call `a_1, ..., a_n ∈ A` a *commuting independent
family* if the elements `a_i` commute pairwise and `P(a_1, ..., a_n) ≠ 0` for every nonzero `P ∈ k[x_1, ..., x_n]`.
Here a constant `c` is evaluated as `c · 1_A`.

**Claim.** Suppose `A` has a commuting independent family of size `n`. Put `K = k(y_1, ..., y_n)` and
`R = A ⊗_k K`. Then:
- the left `R`-module `Q = R / (R z_1 + ... + R z_n)`, with `z_i = a_i ⊗ 1 - 1 ⊗ y_i`, has a free resolution of
  length `n`;
- `Ext^n_R(Q, R) ≠ 0`, so `pd_R Q = n`;
- `Tor^R_n(Q', Q) ≠ 0` for the right module `Q' = R / (z_1 R + ... + z_n R)`.

Hence `w.gl.dim R >= n` and `l.gl.dim R >= n`. The mirror argument gives `r.gl.dim R >= n`.

**Non-unital embeddings count.** Let `φ : k[x_1, ..., x_n] -> A` be any injective `k`-algebra map, unital or not.
Then `φ(x_1), ..., φ(x_n)` is a commuting independent family (route, Section 4). So the claim applies to every
embedding of `k[x_1, ..., x_n]`, and of any ring containing it, such as the Laurent ring `k[Z^n]`.
