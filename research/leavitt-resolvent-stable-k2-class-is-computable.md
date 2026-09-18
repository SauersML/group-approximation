---
rg: 2
id: leavitt-resolvent-stable-k2-class-is-computable
kind: claim
title: The isomorphism K_2(R_L) -> Q^x is computable on Steinberg words by a halting search, so condition (ii) of the word-problem reduction holds and St_N(R_L) has solvable word problem whenever K_2(N,R_L) injects into K_2(R_L)
distinct_from:
  st-n-leavitt-resolvent-word-problem-reduces-to-k2: that reduces the word problem of St_N(R_L) to injective stability (i) and a computable detector (ii); this proves (ii), so the reduction needs only (i).
  leavitt-resolvent-k-theory-is-shifted-rational-k-theory: that computes K_2(R_L) = Q^x through the Pimsner sequence; this makes the isomorphism effective on words, with no new K-theory.
---

**ESTABLISHED** through `leavitt-resolvent-stable-k2-class-is-computable-proof`. Refereed: gq-referee-a PASS, proof-gap lens (report
8ffbfb9b4, N1 and N2 applied); one referee so far. Elementary given the two nodes named above. No priority is claimed.

**Notation.** `ι : K_2(R_L) -> Q^x` is the isomorphism of `leavitt-resolvent-k-theory-is-shifted-rational-k-theory`,
with `ι{λ, N+c} = λ` for every `c >= 1`. For `λ in Q^x`, `{λ, N+1}_M` is the explicit Steinberg word
`h_12(λ(N+1)) h_12(λ)^-1 h_12(N+1)^-1` in `St_M(R_L)`, written with the ring words for `λ`, `λ^-1`, `N+1` and
`(N+1)^-1 = A`. Here `1/m = t_2 t_1^(m-1) A s_1^(m-1) s_2`.

**Statement.** Let `N >= 3`.
1. **A halting search.** Given a word `w` of `St_N(R_L)` whose image in `E_N(R_L)` is `1`, enumerate triples
   `(M, λ, d)`: an integer `M >= N`, a rational `λ != 0`, and a derivation `d` of the equality
   `w = {λ, N+1}_M` in `St_M(R_L)` from the Steinberg relations. The search halts, and the `λ` it finds is `ι[w]`.
2. **Condition (ii) holds.** So `ι`, composed with the stabilization `K_2(N, R_L) -> K_2(R_L)`, is computable from
   words. It is injective on the image of `K_2(N, R_L)`, since `ι` is an isomorphism. `Q^x` has solvable word problem.
   This is condition (ii) of `st-n-leavitt-resolvent-word-problem-reduces-to-k2`, item 3.
3. **Gate 1 reduces to (i).** If `K_2(N, R_L) -> K_2(R_L)` is injective, then `St_N(R_L)` has solvable word problem.
   Moreover `K_2(N, R_L) = {{λ, N+1}_N : λ in Q^x} ≅ Q^x`.
4. **The splitting without (i).** `λ -> {λ, N+1}_N` is a homomorphism `Q^x -> K_2(N, R_L)` and a section of the
   stabilization onto `K_2(R_L) ≅ Q^x`. So `K_2(N, R_L) = U_N ⋊ Q^x`, with `U_N` the kernel of stabilization. It is a
   direct product if `K_2(N, R_L)` is central, which is the OPEN `k2-central-in-steinberg-groups-of-leavitt-resolvent-ring`. The
   word problem of `St_N(R_L)` is solvable if and only if nontriviality in `U_N` is recursively enumerable. Membership
   in `U_N` is decidable, by the word problem of `E_N(R_L)` and the search of item 1, so this concerns a decidable
   set of words (gq-referee-a, N1). So (i),
   `U_N = 1`, is sufficient, and the `Q^x` part is never an obstruction.

## Remarks

- The search uses no ring-level residue. It uses only that equalities in `St_M(R_L)` are recursively enumerable,
  because `R_L` has solvable word problem, together with the Pimsner fact that every stable class is a unique
  `{λ, N+1}`. It gives no time bound.
- **The same principle in general.** Let `R` have solvable word problem, and let `φ : H -> K_2(R)` be a bijective
  homomorphism from a group `H` with solvable word problem, computable from elements of `H` to Steinberg words. Then
  `φ^-1` is computable on words of `K_2(N, R)`.
- A closed-form detector, such as a total residue or a tame symbol at `N = ∞`, would give a bound but is not needed.
