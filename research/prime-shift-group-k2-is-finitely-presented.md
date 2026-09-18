---
rg: 2
id: prime-shift-group-k2-is-finitely-presented
kind: claim
title: The prime-shift group K_2 = <GL_2(Z), diag(2,1), σ_2> is finitely presented
distinct_from:
  prime-shift-kn-fp-reduces-to-a-metabelian-quotient: that proves finite presentation of K_n forces a one-sided relation between e and the prime dilations modulo GL_n(Z); this is the open question whether K_2 is finitely presented.
  prime-shift-affine-group-a1-is-finitely-presented: that is the affine analogue, refuted by deep-denominator germs; the germ argument has no analogue here (item 5 of the reduction).
  gl-n-q-in-permutational-boone-higman-class: that is the type (A) target; finite presentation of K_2 is one of its two open inputs for n = 2.
artifacts:
  - research/artifacts/gq-ring-fp-simple-k2-hidden-relation-search.md
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
- **Attempt 4 (2026-09-18, gq-ring-fp-simple): bounded MSI search for the hidden relation. None found.**
  This is evidence, not proof. The details, code and outputs are in the artifact
  `gq-ring-fp-simple-k2-hidden-relation-search.md`.
  - *Searched.* Words in the generators `σ_2^j X^(±1) σ_2^-j` and `σ_2^j Y^(±1) σ_2^-j`, plus `W` and `D`, all in `N`:
    - for `|j| <= 1`, lengths <= 5 completely and length 6 partially: 1.64 million elements up to probe
      equality;
    - for `|j| <= 2`, lengths <= 4;
    - with the shears `X^(±2)` and `Y^(±2)` added, lengths <= 4.
  - *Tests.*
    - A left-linear key finds words `V_1`, `V_2` with `V_1 = L V_2` for some linear `L`. Such an `L` would
      put `|det L|` in `I_2`, and `|det L| != 1` would be a hidden relation.
    - An `r`-translated key finds `V = L r V'`, giving `|det L|/2 in I_2`.
  - *Result.* No hit of either kind.
    - "No hit" is sound for the searched words, apart from the listed overflow words: a true relation agrees
      on the probe points, and deduplication by probe images loses nothing.
    - The calibration mode, which adds `e`, finds the expected hits. The independent verifier (sympy) passes
      its controls.
  - *Near misses.* Thousands of words fix both axes and `(1,-1)`. None agrees with `r` on any other probe.
  - *Reading.* Consistent with `I_2 = 1`, and hence with `K_2` not finitely presented. It says nothing
    about longer words, `|j| >= 3`, or conjugators other than powers of `σ_2`. Stopped at the budget.
  - **Correction (Attempt 5): this search was structurally blind.** Every searched word preserves content,
    so both tests are vacuous by a two-line argument. The "no hit" above carries no evidence.
- **Attempt 5 (2026-09-18, gq-ring-fp-simple): the near misses point to content, which N does not preserve.
  No separating invariant.**
  - **Generators of N (rigorous).** `N = <σ_2^j SL_2(Q) σ_2^-j, D : j in Z>`, where `D = diag(-1,1)`.
    - `⊇`: `N` is normal and contains `SL_2(Q)` and `D`.
    - `⊆`: the right side contains `GL_2(Z)`, and `σ_2` permutes its generators.
    - `diag(q,1)` normalizes each `σ_2^j SL_2(Q) σ_2^-j`, because `σ_2^-j diag(q,1) σ_2^j = diag(σ^-j q, 1)`.
    - `GL_2(Q) = <SL_2(Q), diag(q,1)>`, so the right side is normal in `K_2 = <GL_2(Q), σ_2>`.
  - **Content (rigorous).** The subgroup `N_0 = <σ_2^j GL_2(Z) σ_2^-j>` preserves the content `c(w)`, since
    `c(σ_2 w) = σ(c(w))`. So does every word of Attempt 4.
    - `r` does not: `c(r(1,1)) = c(168,-10) = 2`. Hence `r ∉ N_0`.
    - Both tests of Attempt 4 were therefore vacuous. A content-preserving linear map lies in `GL_2(Z)`, and
      `L r` is never content-preserving. The artifact records the correction.
  - **Tabulation (one MSI run, 55 s).** On the lines `(1,1)`, `(1,2)`, `(2,1)`, `(1,3)`, `(3,1)`, `(2,3)`, `(1,-2)`:
    - all 185 near misses keep content with ratio 1 and keep no line;
    - `r` keeps no line and doubles content on `(1,1)` and `(1,3)`.

    So the only visible invariant of the near misses is content.
  - **Why content cannot separate.** `SL_2(Q) ⊆ N` changes content. For example
    `x_21(1/2)(1,0) = (1, 1/2)` has content `1/2`. So "`N ∩ Fix(ℓ_x, ℓ_y, ℓ_-)` preserves content" is not
    implied by anything known, and is probably false: commutators of rational shears with elements of `N_0`
    that fix the lines are natural candidates to violate it. They were not checked.
  - **What a separating invariant must satisfy.** It must be invariant under every `σ_2^j SL_2(Q) σ_2^-j`.
    `SL_2(Q)` is transitive on nonzero vectors, and has only the determinant as an invariant of vector pairs.
    Pair determinants fail by Attempt 1, and content fails as shown. So such an invariant must use
    `σ`-twisted structure that no single `SL_2(Q)` sees.
  - **Status.** No conjecture of the requested form survives. The informative search would use the
    generators `σ_2^j x_12(q) σ_2^-j` with rational `q`; it was not run, since no budget was granted for it.
    Stalled.
- **Attempt 6 (2026-09-18, gq-ring-fp-simple): a rational-shear search with a blindness pre-check. No
  relation found.** This is evidence, not proof; details in the artifact
  `gq-ring-fp-simple-k2-hidden-relation-search.md`, second round.
  - *Generators.* `σ_2^j x_12(q) σ_2^-j`, `σ_2^j x_21(q) σ_2^-j`, `W` and `D`, all in `N` by Attempt 5:
    - `|j| <= 1`, `q ∈ {±1, ±2, ±1/2}` or `{±1, ±2, ±1/2, ±3, ±1/3}`;
    - `|j| <= 2`, `q ∈ {±1, ±2, ±1/2}`.

    Length 3 is complete in each case, and length 4 is covered partially, with 0.44 to 0.52 million
    elements per run.
  - *Pre-check.* The generators preserve `p`-content for `p` outside a finite set `S ∋ 2`, and preserve
    `Z[1/S]^2`. `r` preserves both, since it changes content only at 2.
    - Full content and pair determinants are not invariants of the searched group.
    - `r` violates no invariant known from Attempts 1–5, so neither test is blind.
  - *Calibration inside the searched group.* The planted target `X(-1) ∘ σ_2^-1 X(1) σ_2` is found 39 times
    out of 39, with `|det L| = 1`. Between 902 and 3,884 words are linear of determinant `±1` other than `±I`,
    per run.
  - *Result.* No linear relation with `|det L| != 1`, and no `r`-translated match. This is bounded evidence,
    consistent with `2 ∉ I_2`; membership of `r` in `N` is open.
