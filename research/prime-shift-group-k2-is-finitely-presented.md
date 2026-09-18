---
rg: 2
id: prime-shift-group-k2-is-finitely-presented
kind: claim
title: The prime-shift group K_2 = <GL_2(Z), diag(2,1), σ_2> is finitely presented
distinct_from:
  prime-shift-kn-fp-reduces-to-a-metabelian-quotient: that proves finite presentation of K_n forces a one-sided relation between e and the prime dilations modulo GL_n(Z); this is the open question whether K_2 is finitely presented.
  prime-shift-affine-group-a1-is-finitely-presented: that is the affine analogue, refuted by deep-denominator germs; the germ argument has no analogue here (item 5 of the reduction).
  gl-n-q-in-permutational-boone-higman-class: that is the type (A) target; finite presentation of K_2 is one of its two open inputs for n = 2.
---

**OPEN.** Is `K_2 = <GL_2(Z), e = diag(2,1), σ_2> <= Sym(Q^2)` finitely presented?
Notation as in `gl-n-q-lies-in-prime-shift-permutation-group`.

**What is known.**
- `K_2` is finitely generated and contains `GL_2(Q)`.
- The HNN group `Π_2` mapping onto it is not finitely presented
  (`prime-shift-hnn-groups-are-not-finitely-presented`).
- By `prime-shift-kn-fp-reduces-to-a-metabelian-quotient`:
  - `K_2 = K_2^0 ⋊ <σ_2>`, and the centre of `K_2^0` is the scalar group;
  - `K_2/<<GL_2(Z)>> ≅ (Q_>0/I_2) ⋊_σ Z`;
  - if `K_2` is finitely presented, then `e · diag(r,1)^-1 in <<GL_2(Z)>>` for
    some finite product `r` of primes `p_k` taken all from `k >= 1` or all from
    `k <= -1`.
- So a negative answer follows from any quotient of `K_2` that kills `GL_2(Z)`
  and in which no such relation holds, for example one in which every element of
  `I_2` is a square. A positive answer needs such a relation, which lies outside
  the HNN presentation.

**If the answer is yes,** the next test is whether the action of `PK_2` on
`P^1(Q)` has a finitely generated point stabilizer. That is type (A) for `n = 2`.

## Attempts

- **Attempt 1 (2026-09-18, gq-ring-fp-simple): an obstruction through germs or
  quotients. Not reached.**
  - **Point germs.** Any germ on a `GL_2(Z)`-invariant set of points through
    which `GL_2(Z)` acts trivially is blind to `e` (item 5 of the reduction). The
    domain "one coordinate uniquely deepest" is not closed under `x_21(1)`.
  - **Content.** The content homomorphism onto `Z ≀ Z` exists for
    `<GL_2(Z), 2I, σ_2>`, which is therefore not finitely presented. It does not
    extend to `K_2`, because `e` changes content depending on the direction.
  - **Pair determinants and tree types.** For `g = [[1,1],[1,2]] in SL_2(Z)`, the
    element `h = σ_2 g σ_2^-1` lies in `<<GL_2(Z)>>`. It agrees on both coordinate
    axes with `L = [[1,1],[1,p_1]]`, since `h(x,0) = (x,x)` and
    `h(0,y) = (y, σ(2) y)`. So an element of the normal closure multiplies the
    determinant of each axis pair by `p_1 - 1`. No determinant of pairs is invariant under the normal closure. With the
    example indexing `p_1 = 3` the factor is `2`, so the `2`-adic Bruhat--Tits
    type of pairs is not invariant either.
  - **Averaging the content cocycle.** Heuristic only. `e` changes content by
    `0` or `1` according to the `2`-adic direction. Extending `|det|` would
    need a mean on `P^1(Q)` compatible with `GL_2(Z)`. There is none:
    `PGL_2(Z)` is non-amenable with amenable stabilizers. The `p`-adic Haar
    measures are not transported by `σ`
    (`prime-shift-dilation-normalizers-are-nowhere-continuous`).
  - **A copy of A_1 inside.** `<x_12(1), diag(-1,1), e, σ_2>` preserves the line
    `y = 1` and acts on it as `A_1`, by `τ, ι, δ, σ`. In the coordinate `x/y`, it
    acts the same way on every line `y = c != 0`, with `σ_2` carrying `y = c` to
    `y = σ(c)`. Subgroups of finitely presented
    groups need not be finitely presented, so the refutation for `A_1` does not
    transfer.
  - **Presentation side.** No relation of the one-sided shape was found. Any such
    relation shows `Π_2 -> K_2` is not injective. Deciding that is a Dickson-type
    prime-pattern problem, as for `prime-shift-hnn-map-to-a1-is-injective`.
