---
rg: 2
id: aut-out-free-abelianized-extension-virtually-splits
kind: claim
title: The abelianized extension of Out(F_n) by H_1(F_n) splits over an explicit finite-index subgroup, so the abelian level carries no integral obstruction to virtual sections
distinct_from:
  aut-out-free-abelianized-extension-splits-rationally: that shows the extension class c is killed by n minus one, so it carries no rational obstruction; this shows c restricts to zero on an explicit finite-index subgroup, so it carries no integral obstruction either.
  out-free-groups-virtually-embed-in-aut-free-groups: that asks for a finite-index subgroup of Out(F_n) inside some Aut(F_m); this only removes the abelian-level obstruction to one route to it, virtual sections of Aut(F_n) to Out(F_n), and constructs no embedding.
  aut-free-to-out-free-does-not-virtually-split-in-even-rank: that asserts no virtual section exists in even rank; this shows any proof of it must use the extension beyond the abelian level, as Chen--Salter do for surfaces.
---

**ESTABLISHED** by `aut-out-free-abelianized-extension-virtually-splits-proof`
(lane proof, elementary; gq-referee-a PASS; no novelty claimed).

**Priority.** This is the integral, finite-index form of the finite-coefficient
splitting that Bogopolski--Puga use. They split
`F_n/H → Aut(F_n)/H → Out(F_n)` for a characteristic abelian cover `H`, with
`F_n/H ≅ (Z/k)^n` and `k` coprime to `n − 1`, as quoted from their PDF in
`research/artifacts/bh-out-fn-into-aut-fm-2026-09-12.md` §7. There, `n − 1`
is invertible mod `k`, so `h/(n − 1)` is defined on all of `Aut(F_n)`. Here it
is integral only on `A_n`. Bridson--Vogtmann's survey (arXiv:math/0507612,
§"Maps to and from Out", read from its TeX on MSI) records the
Bogopolski--Puga embedding `Out(F_n) ↪ Out(F_m)`. It does not state whether
`Aut(F_n) → Out(F_n)` virtually splits.

Let `n ≥ 2`, `H = H_1(F_n; Z)`, `π: Aut(F_n) → Out(F_n)`, and let
`h: Aut(F_n) → H` be the Fox determinant crossed homomorphism of
`aut-out-free-abelianized-extension-splits-rationally`, with
`h(φψ) = h(φ) + φ_* h(ψ)` and `h(ι_g) = (n − 1)[g]`.

1. **The subgroup.** `A_n = {φ ∈ Aut(F_n) : h(φ) ∈ (n − 1)H}` is a subgroup of
   finite index containing `Inn(F_n)`. So `Γ_n = π(A_n)` has finite index in
   `Out(F_n)`, and `Γ_n = {[φ] : h(φ) ∈ (n − 1)H}` is well defined on outer
   classes.
2. **An almost-section.** `k = h/(n − 1): A_n → H` is a crossed homomorphism with
   `k(ι_g) = [g]`. Its zero set `K_n = {φ ∈ A_n : k(φ) = 0}` is a subgroup with
   - `K_n ∩ Inn(F_n) = Inn([F_n, F_n])`,
   - `K_n · Inn(F_n) = A_n`.
   So `K_n / Inn([F_n,F_n]) → Γ_n` is an isomorphism, and it is a section of
   `Aut(F_n)/Inn([F_n,F_n]) → Out(F_n)` over `Γ_n`.
3. **The class.** The class `c ∈ H²(Out(F_n); H)` of
   `1 → H → Aut(F_n)/Inn([F_n,F_n]) → Out(F_n) → 1` restricts to `0` on `Γ_n`.
   For `n = 2`, `A_2 = Aut(F_2)`, and the extension splits outright.

## What this settles, and what it does not

- Item 4 of the Attempts of `out-free-groups-virtually-embed-in-aut-free-groups`
  left one abelian candidate obstruction to a virtual section: the integral class
  `c`, of order dividing `n − 1`, "might die on a finite-index subgroup". It
  does. So neither rational nor integral cohomology of the abelianized extension
  can exclude a virtual section of `Aut(F_n) → Out(F_n)`.
- It does **not** give a virtual section. `K_n` is an extension of `Γ_n` by the
  infinitely generated free group `Inn([F_n,F_n]) ≅ [F_n,F_n]`. A splitting of
  this extension over a finite-index subgroup of `Γ_n` gives a virtual section.
  Conversely, a virtual section `s` gives such a splitting when `k∘s` vanishes on
  a finite-index subgroup, or lifts from `H` to a crossed homomorphism into
  `F_n` (gq-referee-a, W1). The converse is not claimed in general. The
  nonabelian part of the question, which is where Chen--Salter's argument for
  surfaces lives, stays OPEN here.
- **Review.** gq-referee-a: PASS for items 1–3, with the W1 wording fix above
  (`research/artifacts/gq-referee-a-aut-out-free-abelianized-extension-virtually-splits.md`,
  329ff16a3).
- It does not touch Boone--Higman for `Out(F_n)` directly
  (`out-free-groups-satisfy-boone-higman`, OPEN).
