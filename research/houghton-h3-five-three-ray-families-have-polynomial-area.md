---
rg: 2
id: houghton-h3-five-three-ray-families-have-polynomial-area
kind: claim
title: "The five three-ray relation families F_3, R_3, B_3, C_3, D_3 of H_3 have polynomially bounded area"
artifacts:
  - research/artifacts/zp-houghton-three-rays-2026-09-18.md
distinct_from:
  houghton-group-h3-has-polynomial-dehn-function: that bounds the area of every null-homotopic word; this bounds five explicit linear-length families, and the two are equivalent by houghton-h3-dehn-polynomial-iff-five-three-ray-families.
  houghton-h3-dehn-polynomial-iff-five-three-ray-families: that is the established equivalence; this is the open bound on the families.
  houghton-far-transposition-commutation-is-superpolynomial: that is a negative statement about far commutations in general H_n; this is a positive bound for the specific three-ray families.
---

With `Φ` as in `houghton-h3-dehn-polynomial-iff-five-three-ray-families` (the
largest area of a member of `F_3, R_3, B_3, C_3, D_3` with indices `<= k`, in the
presentation `P` of `research/artifacts/zp-houghton-pours-2026-09-17.md` §0 with
`n = 3`), there is an integer `d` with `Φ(k) ≼ k^d`.

## Attempts

- 2026-09-18 (swarm-0917-w10-w10-z-follow). This is doubling, recorded in
  `research/artifacts/zp-houghton-three-rays-2026-09-18.md` §§B–C.
  - **Lemma B.4 (proved).** Blowing up every point into two gives an injective
    endomorphism `Δ` of `H_3`, with `Δ(λ_ba) = λ_ba^2` and `Δ(λ_ca) = λ_ca^2`
    exactly. Area transfers with a constant factor `K`. The flip `τ_a` commutes with
    `Δ(g)` whenever `g` fixes `(a,1)`. The hidden-top shift `φ` has explicit letters
    `φ̂(λ_ba) = λ_ac λ_ba λ_ca`. Together these give
    `F_3(2k) <= 4K Area(u_k φ̂(u_k)^(-1)) + Ck` and
    `R_3(2k) <= 2K Area(s_k φ̂(s_k)^(-1)) + Ck`. Here `u_k` is a word of length
    `4k - 2` for a `k`-cycle on `(b,1..k)`, and `s_k = λ_ba^k λ_ac^k`.
  - **Where it stops.** The new relators have depth `k` but are not family members.
    Theorem A bounds them only at scale `16k`, because sorting and canonical words do
    not preserve depth. A depth-local Theorem A would give only a quasi-polynomial
    bound `k^(O(log k))`, and it is not proved. `Δ` maps `Sym_fin` into even
    permutations, and odd-scale transpositions straddle the pairs, so odd scales and
    `B_3`, `C_3`, `D_3` are not reached.
  - **Class killed (Lemma C.1).** The invariant is the ray support. For every member
    of `B_3`, `C_3`, `D_3` (index `>= 2`) and `F_3`, any two words representing the
    commuting parts have intersecting ray supports, since two subsets of size `>= 2`
    of three rays always meet. So "reroute to disjoint ray supports, then commute
    letter by letter" dies at the commute step for `n = 3`.
