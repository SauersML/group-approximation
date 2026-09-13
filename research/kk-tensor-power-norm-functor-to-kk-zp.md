---
rg: 2
id: kk-tensor-power-norm-functor-to-kk-zp
kind: claim
title: The p-fold tensor power with the cyclic shift extends to a non-additive functor N from KK to KK^(Z/p)
distinct_from:
  zp-restriction-trivial-splits-cellular-plus-phantom: that splits objects with contractible restriction by the action element; this constructs a multiplicative induction functor producing Z/p-algebras from ordinary KK-classes.
  nishikawa-petrosyan-equivariant-power-functor: that is the imported literature theorem (equivariant over G, with gamma elements); items 1-3 here are its case G = 1, F = Ω = Z/p.
---

**ESTABLISHED (derivation, lane ex2-uct-norm-functor, 2026-09-13; unreviewed;
standard inputs flagged in the artifacts).**  Let `p` be prime, `G = Z/p`, all
algebras separable, `⊗` minimal, and `N(A) = (A^(⊗p), σ)` with the cyclic
shift `σ`.

1. **Contractible norms.**  If `A ≃_KK 0`, then `N(A) ≃_(KK^G) 0`.
2. **Equivalences.**  If a \*-homomorphism `f : A → B` is a KK-equivalence,
   then `f^(⊗p)` is a `KK^G`-equivalence.
3. **The functor.**  There is a unique functor `N : KK → KK^G` with
   `N(A) = (A^(⊗p), σ)` and `N([f]) = [f^(⊗p)]` for \*-homomorphisms `f`.  It
   is not additive: on `KK(C, C) = Z` and `p = 2`, `N(2) = 3 + χ ∈ R(Z/2)`.
4. **Bootstrap norms.**  `N(B) ⊆ B^G`.
5. **Action element.**  `θ_(N(A)) = [σ]`.  It is `1` on `N(C)` and `N(M_n)`,
   and not `1` on `N(C ⊕ C)`, which has induced summands.

**Credit (lane ex3-uct-tate-diagonal, read from the PDF 2026-09-13).**
- Items 2 and 3 are the case `G = 1`, `F = Ω = Z/p` of Nishikawa–Petrosyan, arXiv:2509.15070v2
  (8 Oct 2025), Theorem 5.10 (3) and its uniqueness statement, imported as
  `nishikawa-petrosyan-equivariant-power-functor`. Item 1 follows from item 3.
- **The odd-`p` gap is repaired by their theorem.**
  - ex-verify2-analysis (a272b661a2, `research/artifacts/ex-review2-analysis-2026-09-13-part12.md`)
    passed Theorems A and B at `p = 2` only. For odd `p`, the partition in part 1 Proposition 1 does
    not commute modulo compacts.
  - Nishikawa–Petrosyan Theorem 5.11 constructs a partition `(N_i)` with `[N_i, N_j]` compact and
    exact `S_N`-symmetry `w(N_(w^(−1) i)) = N_i`. Their Remark 5.12 records that naive averaging fails
    for `N ≥ 3`.
  - So items 1–3 hold for every prime `p` by citation of Theorem 5.10, independently of this lane's
    partition argument.
- They prove more:
  - the power functor over any `G` (`KK_G → KK_(G≀F)`);
  - `γ_(G≀F) = ⊗̂(γ_G)`;
  - an equivariantly c.p.-split Izumi filtration of tensor powers of mapping cylinders (Proposition 5.18).
- New here: items 4 and 5, and the Rokhlin corollary.

**How.**
- Item 1: tensor powers of Kasparov cycles, with a Kasparov partition of unity
  averaged over the shift.  Only the partition is averaged, never the
  operator.  This gives an exactly shift-invariant operator.  A homotopy from
  `id_A` to `0` then norms to an equivariant homotopy.
- Item 2: the mapping-cylinder filtration of `N(Z_f)`.  Its middle layers are
  induced from KK-contractible algebras, since `p` is prime.  Its top layer is
  `N(C_f)`, killed by item 1.
- Item 3: the localization universal property of `KK`.
- Item 4: Rosenberg--Schochet commutative models and the Meyer--Nadareishvili
  description of `B^G`.

**Model test.**  Atiyah's power operation is the case `KK(C, C) = Z`.  There
`N(n) = n + ((n^p − n)/p) ρ`, so for `p = 2`: `N(−1) = χ`, `N(2) = 3 + χ`, and
`N(2)^2 = 10 + 6χ = N(4)`.  The trivial functor `A ↦ (A, id)` fails item 5,
since `θ = 1` on every object.

**Not proved here.**  The cycle-level norm represents `N(x)` for every KK-class
`x`, the sum formula `N(x + y) = N(x) + N(y) + Σ_(free orbits) Ind(…)`, and
`N(x ⊗ x') = N(x) ⊗ N(x')` for general classes.  They hold for
\*-homomorphisms and direct sums of them.  After tensoring with the Tate object,
the norm is additive and exact (`tate-norm-is-additive-exact-and-gamma-compatible`).

**Uses.**
- `o2-tensor-power-shift-is-rokhlin`: the shift on `O_2^(⊗p)` is Rokhlin.
- The Tate part `1_T ⊗ N(A)` of the norm of a non-bootstrap algebra is a
  concrete test object for
  `zp-restriction-and-crossed-product-detect-kk-g-contractibility` (part 2,
  §8).

Proof: `kk-tensor-power-norm-functor-to-kk-zp-proof`.
