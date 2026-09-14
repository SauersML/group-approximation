---
rg: 2
id: kl-pivot-letter-words-inject-over-torsion-free-by-finite
kind: claim
title: A degree-one word with a single letter at the base level and a degree-zero excursion injects every group containing a torsion-free subgroup of finite cyclic index normalized by its coefficients
distinct_from:
  kl-p-square-system-equations-are-individually-solvable: that solves single equations and variable-disjoint subsystems of the square system and leaves every pair sharing an unknown; this solves a connected cyclic chain of n equations in which consecutive equations share an unknown, by Tietze elimination along the chain.
  klyachko-kl-holds-when-all-coefficients-have-infinite-order: that needs every coefficient of the word to have infinite order; this allows the coefficient a and the returning coefficient in a^(-1)H to have finite order, and uses that theorem only for the eliminated equation, whose coefficients lie in the torsion-free subgroup.
  kl-p-power-index-reduces-to-p-nonsingular-square-systems: that reduces every degree prime to p over a subgroup of p-power index to one square system and stops there; this solves the two-level pivot case of such a system at degree one, for every finite cyclic index, not only p-powers.
  krstic-p-nonsingular-equations-inject-locally-p-indicable-groups: that needs the coefficient group to be locally p-indicable; this needs only a torsion-free subgroup H of finite cyclic index normalized by a, with no indicability hypothesis on H.
  kl-cyclic-cover-words-have-an-index-m-core: that passes to the kernel of the degree map for window words C t^m, where the variable acquires degree m; this passes to the kernel of a finite cyclic quotient of the coefficient group, where each copy of the variable keeps degree one.
artifacts:
  - research/artifacts/hl-kl-howie-overlap-2026-09-14.md
---

Let `P` be a group, `H <= P` a **torsion-free** subgroup, and `a in P` an
element normalizing `H` with `a^n in H` for some `n >= 1`; take `n` minimal.
Let `V in H * <t>`, let `b in P` with `ab in H`, and put

    w = t a V b  in  P * <t>,        d = deg_t(V),        deg_t(w) = 1 + d.

Write `sigma(h) = a h a^(-1)`, `z = a^n in H`, `h_i = a^i (ab) a^(-i) in H`, and
for a word `V = c_0 t^(e_1) c_1 ... t^(e_L) c_L` (`c_j in H`) let
`V^(j)(x) = sigma^j(c_0) x^(e_1) sigma^j(c_1) ... x^(e_L) sigma^j(c_L)`.

1. **Exact reduction.** Put `Phi_(n-1)(s) = s` and
   `Phi_i(s) = ( V^(i+1)(Phi_(i+1)(s)) h_i )^(-1)` for `i = n-2, ..., 0`, and

       R(s) = s · V^(n)( z Phi_0(s) z^(-1) ) · h_(n-1)   in  H * <s>.

   Then `deg_s(R) = 1 - (-d)^n`, and

       P ∩ <<w>>_(P * <t>)  =  H ∩ <<R>>_(H * <s>).

   So `P -> (P * <t>)/<<w>>` is injective iff `H -> (H * <s>)/<<R>>` is.
2. **Injectivity at degree zero.** If `d = 0`, then `deg_t(w) = 1`, and for
   every group `G` containing `P`, the map `G -> (G * <t>)/<<w>>` is injective.

By inversion the same holds for `t^(-1) a V b` with `ab in H` and
`deg_t(V) = 0`: its inverse is conjugate to `t b^(-1) V^(-1) a^(-1)`, which has
the stated form with `a' = b^(-1) in aH`.

## Level description

Reduce the coefficients of a word modulo `H` and substitute `t -> 1`. The
*level* of a letter `t^(±1)` is the image in `P/H` of the product of the
coefficients before it. The words of item 2 are exactly those, up to cyclic
permutation, in which:
- every letter sits at level `1` or at level `aH`;
- level `1` carries exactly one letter, of sign `+1`;
- the letters at level `aH` have exponent sum `0`.

A substitution `t -> x t y` with `x, y in P` is an automorphism of `P * <t>`
fixing `P`. So every word that such a substitution brings into this form is
covered as well.

## What it adds

- **A connected system solved.** When `n` is a power of a prime `p`, the square
  system of `kl-p-power-index-reduces-to-p-nonsingular-square-systems` for `w`
  has `|Lambda| = 2`. Its `n` equations form one cycle, each sharing an unknown
  with the next. Adjunction tools (Klyachko, the layered theorem of
  Forester--Rourke) solve equations one new unknown at a time, and every
  ordering of the cycle ends in a closing equation with no new unknown. The
  single pivot letter lets the cycle be cut by Tietze elimination instead.
- **Torsion at sign changes.** If `V` begins with `t^(-1)`, the coefficient
  `a h` between the pivot and `V` is a sign-change coefficient in `aH`. If `V`
  ends with `t^(-1)`, so is the returning coefficient in `a^(-1)H`. Either may have
  finite order, and substitutions only conjugate sign-change coefficients, so
  `klyachko-kl-holds-when-all-coefficients-have-infinite-order` does not
  apply.
- **No shape bound.** `V` may be arbitrarily long, with arbitrarily many sign
  changes. This is beyond the sign-index-two theorem and the length-at-most-five
  results quoted in the artifact.
- **No approximation or indicability input.** Nothing is assumed about `H` beyond
  torsion-freeness, so the theorem covers coefficient groups for which neither
  hyperlinearity nor local `p`-indicability is known.
- **Degree `-1` excursions.** With `d = -2`, `w` has degree `-1`. Item 1
  reduces its injectivity to a degree `1 - 2^n` equation over the torsion-free
  `H`, which no imported theorem solves unless its shape is amenable.

## Remaining gap

Two-level words whose base level carries several letters stay open; see
`kl-two-level-words-over-torsion-free-by-cyclic`.

**ESTABLISHED** through `kl-pivot-letter-words-tietze-chain-proof`. The proof is
elementary: Bass--Serre for the coset kernel, a Tietze isomorphism, and the
imported Klyachko theorem for the final equation. A permutation-group model test
of the rewriting is recorded in the artifact. Not independently reviewed. No
novelty claimed; literature beyond the pins in the artifact was not searched.
