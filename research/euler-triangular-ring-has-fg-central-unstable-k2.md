---
rg: 2
id: euler-triangular-ring-has-fg-central-unstable-k2
kind: claim
refuted_by:
  - euler-ring-rational-symbols-are-infinitely-generated
title: For some l and N >= 5, the kernel K_2(N, T_l) of St_N(T_l) -> E_N(T_l) is a finitely generated central subgroup
distinct_from:
  euler-triangular-steinberg-rf-residual-is-fng: that asks only that the finite residual be finitely normally generated; this stronger K-theoretic statement implies it.
  resolvent-ring-corner-symbols-survive-in-k2: that proves K_2(R_l) contains the infinitely generated symbol group of K_2(Z_(l)); for T_l the expected stable K_2 is K_2(D) ⊕ K_2(Z), with no Z_(l) summand.
---

**OPEN.** There are a prime `l` and `N >= 5` such that `K_2(N, T_l) = ker(St_N(T_l) -> E_N(T_l))` is
central in `St_N(T_l)` and finitely generated.

**Use.** It implies `euler-triangular-steinberg-rf-residual-is-fng`, by route
`euler-triangular-residual-fng-from-fg-central-k2`.

## Attempts

1. **Heuristic (2026-09-18, lane gq-infinite-primes).** Every input below is NOT read at source.
   - (T1) *Triangular rings.* For a ring `[[A, M],[0, B]]`, stable K-theory is `K_*(A) ⊕ K_*(B)` (Berrick and
     Keating, the K-theory of triangular matrix rings). This would give `K_2(T_l) ≅ K_2(D) ⊕ K_2(Z)`. The
     bimodule `M`, and with it `Z_(l)`, would contribute nothing.
   - (T2) *The Euler ring.* By the fundamental theorem for twisted Laurent rings over the regular ring `A`,
     `K_2(D)` is an extension of `ker(1 - σ | K_1(A))` by `coker(1 - σ | K_2(A))`.
     - Localization from `Z[u]` gives `K_2(A)` as `K_2(Z) = Z/2` plus tame symbols in `⊕_k K_1(Z) = ⊕_k Z/2`,
       one for each prime `u + 1 + kl`.
     - `σ` shifts `k`, so the coinvariants are finite.
     - `K_1(A) = A^× = ±<u + 1 + kl : k>`, whose `σ`-invariants are `±1`.
     - So `K_2(D)` would be finite, of order at most about `2^3`.
   - (T3) *Stability and centrality.* `T_l` is left Noetherian: `D` is, and `M` is a finitely generated left
     `D`-module. With a stable-rank bound (Stafford, `sr <= Krull dimension + 1`), van der Kallen's injective
     stability would make `K_2(N, T_l) -> K_2(T_l)` an isomorphism with central kernel for `N` large enough, in
     particular for `N >= sr + 3`.
   - Together, (T1)–(T3) would give this claim for `N` large enough, with `K_2(N, T_l)` finite. The claim
     allows `N` to be chosen, since `St_N(T_l)` is finitely presented for every `N >= 5`.
2. **Refuted (2026-09-18, lane gq-k2-q).** `euler-ring-rational-symbols-are-infinitely-generated`: `K_2(N, T_l)` is not
   finitely generated for any `l` and `N >= 3`.
   - Heuristic (T2) fails. The residues of `K_2(A)` lie in `⊕_k K_1(Q) = ⊕_k Q^x`, not in `⊕_k Z/2`, because the lines
     `π_k` meet over the primes dividing `(k−j)l`.
   - The symbols `{π_0, π_q}` (`q ≠ l` prime) are independent in the `σ`-coinvariants. They are detected by the
     line-weighted residue `Σ_k k·v_q(∂_k z)`, which is shift-invariant by two-dimensional reciprocity.
   - So they are independent in `K_2(D) ⊆ K_2(T_l)`. (T1) and (T3) are not needed for the refutation.
