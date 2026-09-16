---
rg: 2
id: fpbs-infinite-centralizer-forces-price-one-proof
kind: route
title: Quotient the product of the commuting normal subgroups by their finite intersection to get a direct product, then lift twice
target: fpbs-infinite-centralizer-forces-price-one
requires:
  - fpbs-khezeli-products-have-fixed-price-one
  - fpbs-finite-normal-quotient-lifts-price-one
  - fpbs-wq-normal-price-one-subgroup-forces-price-one
artifacts:
  - research/artifacts/fpbs-infinite-centralizer-price-one-2026-09-16.md
---

Complete written proof. It is Theorem C and Corollary C.1 in Section 4 of the
linked artifact.

**wq-normality.** If `M ◁ Gamma` is infinite and `M <= Lambda`, then `Lambda`
is wq-normal in `Gamma`. For every proper `K ⊇ Lambda` and `g notin K`,
`g K g^-1 ∩ K ⊇ M`. This is fact (i) of
`fpbs-amenable-outer-kernel-forces-price-one-proof`.

**Proof.** Let `N, M ◁ Gamma` be infinite with `[N, M] = 1`. Put `Z = N ∩ M`
and `L = N M`.
1. **`Z`.** `Z` is normal in `Gamma`, and abelian since `N` and `M` commute.
2. **`Z` infinite.** Then `Z` is an infinite amenable normal, hence wq-normal,
   subgroup. The consequence stated in
   `fpbs-wq-normal-price-one-subgroup-forces-price-one` gives `Gamma` fixed
   price one.
3. **`Z` finite.**
   - `L` is normal in `Gamma`.
   - `N/Z` and `M/Z` commute, generate `L/Z` and meet in `(N ∩ M)/Z = 1`.
   - So `L/Z ≅ N/Z x M/Z`, a product of two infinite groups.
4. **`L/Z` has fixed price one** by `fpbs-khezeli-products-have-fixed-price-one`.
5. **`L` has fixed price one** by `fpbs-finite-normal-quotient-lifts-price-one`,
   since `Z ◁ L` is finite.
6. **`Gamma` has fixed price one.** `L ⊇ N` is wq-normal in `Gamma`, and
   `fpbs-wq-normal-price-one-subgroup-forces-price-one` applies.

**Centralizer form.** If `N ◁ Gamma` is infinite, then
`M = C_Gamma(N)` is normal, since
`gamma C_Gamma(N) gamma^-1 = C_Gamma(gamma N gamma^-1)`, and it commutes with
`N`. So an infinite centralizer gives fixed price one.

**Outer kernel.** If `pi(gamma)` lies in the outer kernel, there is `a in N`
with `c_gamma = c_a` on `N`. Then `a^-1 gamma in C_Gamma(N)`. So
`Q_0 = pi(C_Gamma(N))`, and infinite `Q_0` forces infinite `C_Gamma(N)`.

**Commuting modulo a finite subgroup.** Suppose instead `F = [N, M]` is
finite.
- `F` is normal, since `gamma [n, m] gamma^-1 = [gamma n gamma^-1, gamma m gamma^-1]`.
- In `Gamma/F`, the images of `N` and `M` are infinite normal subgroups that
  commute. The proof above gives `Gamma/F` fixed price one.
- `fpbs-finite-normal-quotient-lifts-price-one` lifts it to `Gamma`.

This is dependency bookkeeping for a written proof, not a formal verification.
