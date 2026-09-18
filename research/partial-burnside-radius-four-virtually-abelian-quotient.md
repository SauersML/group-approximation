---
rg: 2
id: partial-burnside-radius-four-virtually-abelian-quotient
kind: claim
title: The radius-four partial Burnside group of exponent five has an infinite virtually abelian quotient, so its local restricted Burnside radius is at least five
distinct_from:
  partial-burnside-presentations-are-golod-shafarevich: that refutes small radii with finite p-groups when a prime power q dividing N has q >= 4R + 5, which gives nothing for N = 5; this refutes radius four at N = 5 with an infinite linear group whose finite quotients have elements of every prime order q != 5
  lef-burnside-approximants-are-nonlinear-and-nonsolvable: that shows approximants of an infinite LEF Burnside group are eventually nonsolvable and of unbounded linear degree, an ineffective limit statement; this is an explicit metabelian-by-finite linear group satisfying the exponent-5 law on the 4-ball, a lower bound on the radius at which solvable refutations die
  local-restricted-burnside-iff-partial-burnside-finite-quotients: that reformulates LRB(m,N) through the partial Burnside groups; this computes a lower bound R*(2,5) >= 5 for the witness radius there
artifacts:
  - experiments/partial-burnside-census-2026-09-17/h5_char0_certificate.py
  - experiments/partial-burnside-census-2026-09-17/verify_h5_quotient.py
  - experiments/partial-burnside-census-2026-09-17/exponent_cohomology.py
  - experiments/partial-burnside-census-2026-09-17/monomial_search.py
---

**ESTABLISHED** through `partial-burnside-radius-four-virtually-abelian-quotient-proof`.

**Setting.** `Π_R(2,5) = F_2/⟨⟨h^5 : 1 <= |h| <= R⟩⟩` as in
`local-restricted-burnside-iff-partial-burnside-finite-quotients`. Let
`O = Z[ζ]`, `ζ` a primitive 5th root of unity, act on `O^5` by affine maps
`(g, c): v -> g v + c`, with product `(g1,c1)(g2,c2) = (g1 g2, c1 + g1 c2)`.
Put `X = diag(1, ζ, ζ^2, ζ^3, ζ^4)`, `Y` the cyclic shift `(Y v)_i = v_{i+1}`
(indices mod 5), and

    a = (X, (0, 0, -ζ^2, 1, 0)),     b = (Y, 0).

**Statement.**
1. `h(a,b)^5 = 1` for every reduced word `h` of length `<= 4` (160 words), and
   `(a^2 b a b^{-1})^5` is the translation by `(0, 0, 0, 5(1 + ζ^3), 0)`.
2. `Q = ⟨a, b⟩` is an infinite quotient of `Π_4(2,5)`. Its translation subgroup
   `T = Q ∩ O^5` is a nonzero free abelian group of index `<= 125`, and
   `Q/T` embeds in the Heisenberg group `⟨X, Y⟩` of order 125. So `Q` is
   virtually abelian and linear over `Z`.
3. For every prime `q != 5`, `Π_4(2,5)` has a finite quotient containing an
   element of order `q`. So `Π_4(2,5)` has finite quotients that are not
   5-groups, and of unbounded order.
4. Hence `LRB(4, C)` fails for every `C`, and the witness radius `R*` of clause 3
   of `local-restricted-burnside-iff-partial-burnside-finite-quotients` satisfies
   `R*(2,5) >= 5`. The Golod--Shafarevich bound gives no lower bound at `N = 5`.

## Attempts

1. **Scope of the obstruction (computation, evidence only).** The law system for
   abelian-by-5-group quotients `W ⋊ P` is linear in the cocycle:
   `N_{ρ(w)} c(w) = 0` for `|w| <= R`, with `N_g = 1 + g + ... + g^4`. A solution
   space larger than the coboundaries gives a non-5-group quotient
   (`exponent_cohomology.py`, `monomial_search.py`).
   - For `P = H5` on its 5-dimensional module, every one of the 480 markings has
     solution dimensions `8, 6, 6, 6, 5, 5` at `R = 1..6` against 5 coboundaries
     (`q = 11, 41`). The quotient dies at `R = 5`.
   - For all 2-generated `P = ⟨Y, diag(ζ^e) Y^k⟩` inside
     `{sum-zero diagonals} ⋊ C5` (up to shift and scaling of `e`; this includes
     the maximal class groups of order `5^5`), the last radius with a
     non-coboundary solution is at most 4. The summaries agree for
     `q = 11, 31, 101`.
   - So radius 5 is not refuted by these families. Larger modules and larger
     5-groups (quotients of `R(2,5)`) are untested.
2. **Permutation censuses are blind here.** The low-index census of
   `experiments/partial-burnside-census-2026-09-17` finds only 5-group images of
   `Π_3(2,5)` up to degree 20 (4,085,416 search nodes). `Π_4(2,5)` is a quotient
   of `Π_3(2,5)`, so by clause 3 `Π_3(2,5)` still has non-5-group finite
   quotients, and every transitive action of degree `<= 20` of such a quotient
   has a 5-group image. The minimal faithful degree of these affine quotients was
   not computed.
   A low-index census at a fixed radius is therefore no evidence for "only
   5-group quotients" at that radius: the hypothesis "`Π_3(2,5)` has only
   5-group finite quotients", suggested by the census, is false.
