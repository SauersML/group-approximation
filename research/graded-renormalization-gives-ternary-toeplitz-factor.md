---
rg: 2
id: graded-renormalization-gives-ternary-toeplitz-factor
kind: claim
title: A homeomorphism with a height-3 self-renormalization that cycles a clopen 3-colouring factors onto the ternary valuation Toeplitz subshift; in nV this would give an infinite finitely generated periodic subgroup
distinct_from:
  smart-induced-map-has-brick-local-height-3-renormalization: that proves SMART's induced map has a height-3 renormalization; this says what extra structure (a colouring cycled by the renormalization) turns such a renormalization into a Toeplitz factor, and `smart-renormalization-admits-no-graded-basins` shows SMART's renormalization lacks it.
  nv-periodic-groups-via-schreier-subshift-factors: that reduces periodic subgroups of nV to a factor onto a Grigorchuk-type subshift; this gives a checkable sufficient condition for such a factor, stated purely in terms of the dynamics of one element.
  renormalizable-thompson-elements-give-baumslag-solitar: that turns a brick-local renormalization into a Baumslag–Solitar subgroup; this turns a graded renormalization into a Toeplitz factor, and needs no brick-locality of the renormalizing map.
---

**ESTABLISHED** by `graded-renormalization-gives-ternary-toeplitz-factor-proof` (lane proof, bh-free-01,
elementary, not independently reviewed; no priority claimed). The group-theoretic consequence (item 3) uses
Nekrashevych, arXiv:1601.01033 (TeX read on MSI 2026-09-18): Theorem `th:main` and Proposition
`prop:embeddingfull`.

## The ternary Toeplitz subshift

`T_3 ⊂ {0,1,2}^Z` is the set of sequences `s` for which some `x ∈ Z_3` satisfies
`s(m) = v_3(m + x) mod 3` for every `m` with `m + x ≠ 0`. (If `x ∈ Z`, the letter at `m = −x` is
unconstrained.) It is closed and minimal (proof, step 3). Remark, not used: it is the substitution subshift
of `0 → 001, 1 → 002, 2 → 000`.

## Statement

Let `g` be a homeomorphism of a Cantor space `A`. Suppose there are clopen sets `D ⊆ A` and
`A = L_0 ⊔ L_1 ⊔ L_2`, and a homeomorphism `Ψ : A → D`, such that:

- **(R1)** `A = D ⊔ gD ⊔ g²D`;
- **(R2)** `Ψ ∘ g = g³ ∘ Ψ` on `A` (so the first-return map of `g` to `D` is `Ψ g Ψ^{-1}`);
- **(R3)** `gD ∪ g²D ⊆ L_0`;
- **(R4)** `Ψ(L_c) ⊆ L_{c+1}` for `c ∈ Z/3`.

Then:

1. For every `y ∈ A` the itinerary `I(y) = (c : g^m y ∈ L_c)_{m ∈ Z}` lies in `T_3`, and `I` is a factor map
   `(A, g) → (T_3, σ)`.
2. **Necessity (Lemma A).** Conversely, for any Cantor system `(A, g)` and any factor map `J` onto
   `(T_3, σ)`, let `p : T_3 → Z_3` be the odometer factor. The composite `p ∘ J` fails to be open at every
   point of `J^{-1}(hole orbit)`. Near such a point only one class of `v_3(p∘J − p∘J(y_0))` mod 3 occurs.
   So some rigidity at the holes is forced. (R3) and (R4) are a renormalization-compatible form of it, and
   `Ψ` is not required to be brick-local or to lie in `nV`.
3. **Periodic groups in nV.** Suppose `g` is an element of `nV` and `A ⊆ C^n` is a `g`-invariant clopen set.
   Let `G = ⟨h_1, h_2, b⟩` be Nekrashevych's fragmentation of the dihedral action `a(x) = −x`, `b(x) = 1 − x`
   on `Z_3`, where `h_i` act as `a` on the pieces `P_j = {x ≠ 0 : v_3(x) ≡ j mod 3}` according to
   `{000, 110, 101, 011}`. Then `G` is an infinite, finitely generated, periodic group, and `G` embeds in
   `nV`. So `brin-thompson-groups-contain-infinite-periodic-groups` follows from
   `some-nv-element-has-a-graded-height-3-renormalization`.

## Scope

- The criterion needs only one element `g` of `nV`. `Ψ` may be any homeomorphism.
- SMART's landed renormalization fails (R3) and (R4) for every choice of colouring
  (`smart-renormalization-admits-no-graded-basins`).
