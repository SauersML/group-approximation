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
- **Attempt 2 (2026-09-18, gq-infinite-primes): one explicit element decides whether `e` is in `N`.
  Not decided.**
  - *Axis agreement.* Let `g = [[a,b],[c,d]] in GL_2(Z)`, `j in Z`, and `σ^j(g) = [[σ^j a, σ^j b],[σ^j c, σ^j d]]`.
    Since `σ` is multiplicative with `σ(0) = 0`, `h = σ_2^j g σ_2^-j in N` agrees with the matrix `σ^j(g)` on
    both coordinate axes. Its determinant `D = σ^j(ad) - σ^j(bc)` is nonzero, because `σ^j` is injective
    and `ad != bc`.
  - So `k = σ^j(g)^-1 h` fixes both axes pointwise, and `σ^j(g) ≡ diag(D,1)` modulo `SL_2(Q) ⊆ N`. Hence
    `diag(D,1) · k in N`. Every pair `A - B = ±1` occurs as `(ad, bc)`, for `g = [[A,B],[1,1]]`. This
    generalizes the `p_1 - 1` example of Attempt 1 to all `g` and `j`.
  - *The reformulation.* With the example indexing `p_1 = 3`, take `j = 1` and `g = [[2,1],[1,1]]`. Then
    `σ(g) = [[3,1],[1,1]]`, `D = 2`, and `e ≡ k^-1` modulo `N` for the explicit element
    `k = σ(g)^-1 σ_2 g σ_2^-1`, which fixes both axes pointwise. So `e in N` if and only if `k in N`. In
    that case `I_2 = Q_>0` and `K_2/N ≅ Z`, and item 4 of the reduction is met with the empty product.
  - *The axis character does not decide it.* On the stabilizer of the `x`-axis, `k'(t,0) = (σ^(d(k'))(t) χ(k'), 0)`
    defines `χ`, a homomorphism to `Q^x` on the degree-0 part with `χ(diag(r,1)) = r`. It vanishes on
    pointwise axis-fixers. By the axis agreement, `χ(N ∩ Stab)` contains every `D` above, among them `2`.
    So `χ` cannot separate `e` from `N`. A decision needs an invariant of the pointwise axis-fixers.
- **Attempt 3 (2026-09-18, gq-ring-fp-simple): a third fixed line, and a reduction to three-line fixers.
  Not decided.** Notation of Attempt 2, with `p_1 = 3`, `σ(5) = 2`, `σ(11) = 5`. Put `ℓ_x`, `ℓ_y` for the axes
  and `ℓ_- = Q(1,-1)`. Let `A_3` be the elements of `K_2^0` that fix `ℓ_x`, `ℓ_y` pointwise and map `ℓ_-` to
  itself; they act on `ℓ_-` by a scalar `χ_3`, a homomorphism `A_3 -> Q^x`.
  - **A family in `A_3`.** Take `g = [[a, a-1],[1,1]] in SL_2(Z)` and `j in Z`, and put
    `n = σ^j(g)^-1 σ_2^j g σ_2^-j`.
    - `g(1,-1) = (1,0)` is fixed by `σ_2^j`.
    - So `n(1,-1) = σ^j(g)^-1(1,0) = (1,-1)/D` with `D = σ^j(a) - σ^j(a-1) = det σ^j(g)`.
    - Hence `n in A_3`, `χ_3(n) = 1/D`, and `diag(D,1)·n in N`.
    - The element `k` of Attempt 2 is `a = 2`, `j = 1`: it fixes both axes pointwise and halves `ℓ_-`.
  - **Members of `N ∩ A_3` found have `χ_3 = ±1`.** Example: `g = [[11,10],[1,1]]`, `j = 1`. Then
    `σ(g) = [[5,6],[1,1]]` has determinant `-1`, so `n in N`, and `n(1,-1) = -(1,-1)`.
    - This is consistent with the class map `A_3 -> K_2^0/N` being `|χ_3|` on the family, which is
      what `I_2 = 1` would predict.
    - It is not a proof: `N ∩ A_3` is not understood.
  - **Reduction to three-line fixers (rigorous).**
    - The involution `M = [[1,0],[-1,-1]] in GL_2(Z)` swaps `ℓ_x` and `ℓ_-` and preserves `ℓ_y`. The swap
      `(x,y) -> (y,x)` swaps the axes and preserves `ℓ_-`.
    - Conjugating `k` by these gives elements with scalars `(1/2,1,1)`, `(1,1/2,1)` and `(1,1,1/2)` on
      `(ℓ_x, ℓ_y, ℓ_-)`, all with the same class as `k` in the abelian group `K_2^0/N`.
    - Their product times `2I` is an element `r` fixing all three lines pointwise, with `r ≡ e^-1` mod `N`:
      its class is `(1/2)^3 · 2^2 = 1/2`, since `|det(2I)| = 4`.
    - So `e in N` if and only if this three-line fixer `r` is in `N`. Either `e in N`, or the class of an
      element is not a function of its scalars on three lines.
  - **Why no scalar formula can decide it.** A homomorphism `F(λ_x, λ_y, λ_-)` that is symmetric under the
    `S_3` above and equals `χ_3` on the family must be `λ_x λ_y λ_-`. That gives `c^3` on `cI`, while its class is
    `|det| = c^2`, and `c^3 = c^2` in `Q_>0/I_2` for `c = 1/2` exactly when `e in N`. So if `e ∉ N`, no
    scalar formula on these three lines computes the class, and a separating invariant must use the action
    off them.
  - **Status.** Stalled after this attempt, per the stall rule. Membership of `k`, equivalently of `r`, is
    open. The Bieri--Strebel test (`prime-shift-kn-fp-reduces-to-a-metabelian-quotient`) and
    `torus-amalgams-of-adelic-groups-are-not-finitely-presented` still apply unchanged.
