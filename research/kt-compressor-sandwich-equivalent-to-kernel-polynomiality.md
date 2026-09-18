---
rg: 2
id: kt-compressor-sandwich-equivalent-to-kernel-polynomiality
kind: claim
title: The compressor sandwich for the Theorem E pair is equivalent to its kernel case, polynomiality of Mon-stable overgroups inside EL_r(R)
distinct_from:
  kt-compressor-stable-polynomial-content-overgroups-are-gamma: that is the open sandwich claim for Δ ≤ EL_r(R) ⋊ SL_d(Z); this proves the non-kernel part of it and shows the whole claim is equivalent to the kernel statement
  kt-compressor-stable-overgroups-have-polynomial-content: that fixes the root contents and proves the projection dichotomy {±I} or Zariski dense; this removes the Zariski-dense case entirely, conditionally on the kernel statement
  kt-compressor-stable-kernel-overgroups-are-polynomial: that is the open kernel statement; this is the equivalence with the sandwich claim
---

**ESTABLISHED (proposed; proof in `kt-compressor-sandwich-equivalent-to-kernel-polynomiality-proof`).**
Notation as in `kt-compressor-stable-overgroups-have-polynomial-content`:
`A = F_q[x_1,…,x_d] ⊂ R = F_q[x_1^(±1),…,x_d^(±1)]`, `r,d ≥ 3`,
`Γ = EL_r(A) < G = EL_r(R) ⋊ SL_d(Z)`, `Mon = SL_d(Z) ∩ M_d(N)`, `N = EL_r(R)`.
Call a subgroup `Δ ≤ G` *admissible* if

```text
Γ ≤ Δ,     P Δ P^(-1) ≤ Δ for all P ∈ Mon,     e_12(f) ∈ Δ ⇒ f ∈ A.
```

The following are equivalent.

* **(S)** Every admissible `Δ` equals `Γ`
  (`kt-compressor-stable-polynomial-content-overgroups-are-gamma`).
* **(K)** Every admissible `H ≤ N` lies in `SL_r(A)`, i.e. has all entries polynomial
  (`kt-compressor-stable-kernel-overgroups-are-polynomial`).

More precisely, for an admissible `Δ` with kernel `H = Δ ∩ N`:

1. `H` is admissible.
2. If `H ≤ SL_r(A)`, then `π(Δ) = {I}` and `Δ = Γ`. The key step: for `(g,P) ∈ Δ`,
   `g·M_r(P·A)·g^(-1) ⊆ M_r(A)`, which forces `P·A ⊆ A`; applied to `(g,P)^(-1)` as well,
   `P` is a permutation matrix, and a finite `Mon`-stable subgroup of `SL_d(Z)` is trivial
   here.
3. **(Entry-ring dichotomy.)** The `A`-span `I(H)` of all entries of all `h ∈ H` is a
   `Mon`-stable subring of `R` containing `A`. So either `H ≤ SL_r(A)` or `I(H) = R`.
   Equivalently, the `A`-linear span of `H` in `M_r(R)` is either `M_r(A)` or `M_r(R)`.

So the Zariski-dense branch of the projection dichotomy never needs separate treatment:
the whole sandwich claim is the statement that `Mon`-stability and polynomial root
contents keep all *entries* polynomial. The same proof works for the weaker version of
(S) used by `kt-pair-floor-reduces-to-wreath-model-via-compressor-sandwich`, with `Mon`
replaced by any compression semigroup containing it.

**Calibration (d = 1, no compressors).** For `A_1 = F_q[t] ⊂ R_1 = F_q[t,t^(-1)]` and
`r ≥ 3`, every subgroup `SL_r(A_1) ≤ H ≤ SL_r(R_1)` is `SL_r(A_1)` or `SL_r(R_1)`. So
the analogue of (K) holds in one variable with no stability hypothesis at all. The proof
is a density argument in `SL_r(F_q((t)))`. It uses that `A_1` is dense in the valuation
ring of a local field with finite residue field and that `SL_r(A_1)` is the full
stabilizer of a vertex. Both fail for `d ≥ 2`: no single valuation `ν` of `R` has
`{f ∈ R : ν(f) ≥ 0} = A`, because that set of monomials is a half-space. This is exactly
where the compressors must enter in (K).

DERIVATION
kt-compressor-sandwich-equivalent-to-kernel-polynomiality-proof
