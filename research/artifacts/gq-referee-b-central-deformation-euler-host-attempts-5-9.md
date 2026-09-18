# Referee report (gq-referee-b, citation/scope lens): T_p Attempts 5–9 on the central-deformation Euler host

**Reviewed.** Attempts 5–9 of `central-deformation-euler-host-has-fng-steinberg-residual` (OPEN; lane gq-k2-q), read on
origin/main (d4e505ddd). The coordinator asked for this review.

**Verdict: PASS.** Every step I checked is correct. I pinned the textbook inputs where a source was reachable
(below). No input is applied to the noncommutative `B` outside its hypotheses. There are four scope and wording fixes,
W1–W4.

## Textbook inputs, pinned

- **Quillen homotopy invariance, and NK vanishing for regular rings.** Source: C. Weibel, *The K-book*, Ch. V, read at
  source on pp. 39–40 (author's PDF).
  - Theorem 6.2 ("Fundamental Theorem of G(R)"): "Let R be a noetherian ring. Then [...] G_n(R) ≅ G_n(R[s]) for all n".
  - Theorem 6.3: "If R is a regular noetherian ring, then the base change K(R) → K(R[s]) is a homotopy equivalence, so
    K_n(R) ≅ K_n(R[s]) for all n. [...] In particular, regular rings are K_n-regular for all n."
  - Remark 6.4.1 points to Quillen [Q341, p. 36].
  - **Noncommutative rings are allowed.** The chapter applies Theorem 6.4, the filtered version, to `U(g)` in
    Example 6.4.2.
  - **The same chapter supports regularity of `D`.** Exercise 6.4, p. 50: "It is well known that R_φ[t] is a regular
    ring when R is", for commutative noetherian `R` with an automorphism `φ`. Then `D = A_σ[x, x^(-1)]` is a
    localization of a regular ring.
  - **`D` meets the hypotheses of Theorem 6.3.** It is left and right noetherian with global dimension `≤ 3`.
  - **Pin.** Attempts 4 and 9 use `K_2(D) ≅ K_2(D[t])` and `NK_2(D) = K_2(D[t], tD[t]) = 0`. Both are Theorem 6.3.
    The same theorem gives `K_i(Z[u]) = K_i(Z)`.
- **Dennis–Stein detector (Attempt 9).** Read at source, LNM 342, p. 255: "if F is a perfect field of characteristic
  p > 0 (including p = 2), then K_2(F[X,Y]/(X^2,XY,Y^2)) ≈ K_2(F) ⊕ F^+ [...] the generators not coming from K_2(F)
  are of the form {1+X_i, 1+uX_j}, i ≠ j, u ∈ F".
  - **Hypothesis.** `F` must be *perfect*. Finite fields are, so "in characteristic `l`" should read "over finite or
    perfect fields of characteristic `l`".
- **Berrick–Keating for `T_p` (check C2).** This is the equality `K_2(T_p) = K_2(B) ⊕ K_2(Z)`, used by Attempt 9's
  "stable `K_2(T_p)` is finite".
  - I read it via C. C. Xi, arXiv:1107.5380v1, Lemma 4.1, p. 8: "If R_i is a ring with identity for i = 1, 2, and if M
    is an R_1-R_2-bimodule, then [...] K_n(S) ≃ K_n(R_1) ⊕ K_n(R_2) for all integers n". The same page credits
    `n = 1, 2` to Dennis–Geller 1976 (report 76fc7667e).
  - There is no hypothesis on `M`, so the noncommutative `B` is fine. Only the primary source is unread.
- **Commutative algebra (Attempt 7).** Not read at source. Theorem numbers are not pinned; the statements are standard.
  - Macaulay's unmixedness theorem: in a Cohen–Macaulay ring, such as a polynomial ring over `Q`, an ideal generated
    by `ht I` elements is unmixed.
  - Serre's criterion: a noetherian ring is reduced if and only if it satisfies `(R_0)` and `(S_1)`.

## Attempt 5: the congruence-subgroup lemma is correct

- **`I_rf ⊆ J`.** For `a ∈ I_rf`, `x_12(a) ∈ St_N(T)_rf` by `steinberg-rf-forces-ring-rf`. Its image `e_12(a)` lies
  in the normal closure of the `ḡ_s`, which sits inside the normal subgroup `GL_N(T, J)`. So `a ∈ J`.
- **W1 (`J ⊆ I_rf`).** The text says "each `g_s` dies in every `St_N(T/J')`".
  - What is needed, and what is immediate, is that `ḡ_s` dies in the *finite* group `E_N(T/J') ⊆ GL_N(T/J')`. So its
    entries lie in `J'`.
  - Finiteness of `St_N(T/J')` itself is true but needs an extra input. Say `E_N`.
- **For `T_p`, the reverse inclusion (supplied).** The text shows only
  `I_rf(T_p) ⊆ [[I_rf(B) ∩ (p−1)B, 0],[0,0]]`. The reverse inclusion also holds.
  - `K = I_rf(B) ∩ (p−1)B` is two-sided, since `p − 1` is central.
  - `K·M = 0`, since `p = 1` on `M`.
  - Under a finite quotient `T_p → F`, the corner `B → eFe` is a unital map to a finite ring, so `K` dies.
  - So `I_rf(T_p) = [[K,0],[0,0]]`. That is what makes "the route needs `K` finitely generated" follow from the
    lemma. Add this line.
- **The Euler-type paragraph.** `p + e_22` is central in `T_p`, and `B[p^(-1)] ≅ D[t^(±1)]`. The image of `K_2(B)` has
  order `≤ 4`, by Attempt 4. Correct.

## Attempt 7: correct

- **Rationally the lamps commute.** `(k−j)l[b_j,b_k] = 0` gives commutation in `B ⊗ Q`.
- **`S_K` is a complete intersection.** It has `1 + |K|` variables and `|K| − 1` equations.
  - The open part `Π π_k ≠ 0` is the 2-dimensional domain `Q[u,p][π^(-1)]`.
  - The fibres over the points `u = −1−kl` are lines.
  - So `dim S_K = 2`, `ht = |K| − 1`, and the unmixedness theorem gives no embedded primes and equidimensionality. The
    1-dimensional lines cannot be components.
- **Domain.** The generic point lies in the reduced open part, so `S_K` is `(R_0)`. Together with `(S_1)`, `S_K` is
  reduced; being irreducible, it is a domain.
  - A directed colimit of domains is a domain.
- **Injectivity.** Apply the dimension argument to each `S_K → A_p^(K) ⊗ Q`: a surjection of affine domains of equal
  dimension is injective. Then pass to the colimit. Phrase it at the finite level.
- **Consequences.** `ker(B → A_p[x^(±1);σ]) = ker(B → B⊗Q)`, the `Z`-torsion, because `A_p` is torsion-free. And
  `A_p[x^(±1);σ] ⊆ D[t]` is residually finite, by integer evaluation of `t` over the torsion-free `D`.

## Attempt 8: computations correct

- **Additive letter.**
  - `h(a) = a(a+l)/(2a+l)`, and `h(a+l) − h(a) = 2l(a+l)^2/((2a+l)(2a+3l))`. Setting this equal to `l` gives
    `l(2a^2 + 4la + l^2) = 0`.
  - At `m_0`, `π_0 = 1`, so `l(2+4l+l^2)m_0 = 0`.
  - `2π_k + l` is invertible because `b_k + b_(k+1)` is a conjugate of an invertible operator.
- **Multiplicative letter.** `π_1π_2 − π_0π_1 = l`, that is `l(2π_1 − 1) = 0`. At `m_0` this gives
  `l(1+2l)m_0 = 0`.
- **In both cases, no `Z_(l)`.** The cofactor is a unit of `Z_(l)`, or even when it is not, `l·m_0` becomes torsion.
- **W2 (title).** "A Baumslag letter cannot remove the torsion" generalizes from the two tested forms, additive and
  multiplicative doubling. The "Why" paragraph is a heuristic for general letters. Title it "Neither Baumslag letter
  (additive or multiplicative) ...", or mark the general statement heuristic.

## Attempt 9: correct as a reduction

- **Grading.** `B_0 = Z[u][x^(±1);σ]`. The relation ideal in degree 0 is generated by the degree-0 relations, since no
  generator has negative degree.
  - `K_2(B) = K_2(B_0) ⊕ K_2(B,B_+)` for the split pair. This is valid for any ring, including the noncommutative
    `B`.
- **Stable vanishing on Euler-type quotients.**
  - `φ` maps the split pair `(B, B_+)` to `(D[t], tD[t])`, and `K_2(D[t], tD[t]) = NK_2(D) = 0` by Weibel V.6.3.
  - Every finite quotient where `p` is a unit factors through `B[p^(-1)]`.
  - So the conclusion holds stably.
- **The grading homotopy `τ`.** Correct. `NK_2(B) = 0` is correctly left as a *hypothesis*. `B` is not known to be
  noetherian or regular, so Weibel V.6.3 does not apply to it. **No mismatch.**
- **W3 (the detector sentence).** "The free lamps of C1 map onto such rings" is imprecise.
  - With `x` present, a map of `B` to a commutative ring forces `b_k = b_(k+1)`.
  - So `B` itself cannot send `b_0 ↦ X` and `b_1 ↦ Y` into `F[X,Y]/(X^2,XY,Y^2)`. Only the lamp subring can, or `B`
    can map to `M_n` of such a ring by C1's block shift, and then one uses Morita invariance.
  - Say which of these is meant.
- **W4.** "Farrell-type non-finiteness" is correctly labelled heuristic. Farrell's theorem is for `NK_1` and is not
  cited here.
