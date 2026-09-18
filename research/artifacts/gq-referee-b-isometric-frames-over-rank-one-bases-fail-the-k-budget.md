# Referee report (gq-referee-b, citation/scope lens): isometric frames over rank-one bases fail the K-budget

**Reviewed.** Both from lane gq-infinite-primes, 74de4d286, read on origin/main:
- `isometric-frames-over-rank-one-bases-fail-the-k-budget` and its `-proof`;
- Attempt 12 of `fp-simple-resolvent-ring-with-divisible-unit-class`.

**Verdict: PASS.** Items 1–4 are correct. Two of the three external inputs are now pinned in Weibel's *K-book*, read
in the author's PDF. There are three fixes:
- W1 is a small statement error;
- W2 is a real scope restriction on item 3;
- W3 concerns the justification in the Examples.

## Pins

- **(BC) Bass cancellation: pinned.** Weibel, *The K-book*, Ch. I, Exercise 1.5, p. 4.
  - The definition: "We say that a ring R satisfies condition (S_n) if for every unimodular row (r_0, r_1, ..., r_n)
    in R^(n+1) there is a unimodular row (r'_1, ..., r'_n) in R^n with r'_i = r_i − r_0 t_i [...] The stable range of
    R, sr(R), is defined to be the smallest n such that R satisfies condition (S_n). (Warning: our (S_n) is the stable
    range condition SR_(n+1) of [Bass].)"
  - Part (b): "If sr(R) = n, show that all stably free projective modules of rank ≥ n are free. Bass' Cancellation
    Theorem [Bass, V.3.5] [...]"
  - Part (a) (Vaserstein): "(S_n) holds for all n ≥ sr(R)."
  - This is for general rings, which covers the Vaserstein/Warfield noncommutative form the node needs. The
    commutative theorem is I.1.3 on p. 3.
  - It matches the route's (BC), provided "stable range `d`" is read in Weibel's `sr` convention, not Bass's `SR_d`.
    State the convention.
- **Quillen for filtered rings: pinned.** Weibel, *The K-book*, Ch. V (read earlier, report d746cbee4).
  - Theorem 6.4: "Let R be a filtered ring such that gr(R) is noetherian and of finite flat dimension d over
    k = F_0 R, and k has finite flat dimension over gr(R). Then k ⊂ R induces G(k) ≃ G(R)."
  - Remark 6.4.1: "If in addition k is regular, then so is R [...] K(k) ≃ K(R)."
  - Example 6.4.2 does `U(g)`.
  - For `A_1(Q)` with the Bernstein filtration, `F_0 = Q` and `gr = Q[x,y]`, so `K_0(A_1(Q)) = Z·[1]`.
  - The node's phrase "filtered rings with regular Noetherian associated graded ring" should be replaced by these
    hypotheses: finite flat dimension, and `F_0 R` regular.
- **Stafford, `sr(A_1(Q)) = 2`: not read.** Only finiteness is needed for (R2). That also follows from Stafford's
  bound `sr ≤ Kdim + 1` for noetherian rings, which is also unread.

## Steps checked

- **Setting check.** Only the ratio `r` is determined. When `m[p] − n[1_B]` is torsion of order `e`, rescaling
  `(m, n)` gives exact equality. Correct.
- **Item 1.** Item 1 of the matricial node holds over any `B`, and then `rational-k1-detection-...` applies.
- **Item 2.** `m[p] = m[1_B]` gives `(pB^k)^m ⊕ B^a ≅ B^(m+a)`. Taking `d` copies and applying (BC) at rank `md ≥ d`
  gives freeness. Correct.
- **Item 3.**
  - `U = Sx` and `V = yT` satisfy `UV = SP_jT = 1` and `VU = yP_jx = yx = 1`.
  - `U ∈ M_j(R_1)`, so the graded node applies to `M_j(R)`: it has a unital `Q`, a grading, and a unit of degree `1`.
  - *Morita.* `λ1_j ↦ j[λ]`, and `{λ : λ^j ∈ K}` is finitely generated if and only if `K` is. It sits between `K`
    and `F ∩ (1/j)K_F` inside the free part `F`.
  - `E_N(M_j(R)) = E_(jN)(R)` for `N ≥ 2`. Correct.
- **Item 4.** Every relation is homogeneous. Correct.

## Fixes

- **W1 (statement, (R1)).** "So `m[p] = n[1_B]` for unique coprime integers `m ≥ 1` and `n ≥ 0`" is false when
  `K_0(B)` has torsion.
  - For example, `m[p] − n[1_B]` can be a nonzero torsion element for the coprime pair.
  - The route's Setting check already handles this. Change the statement to: "for some integers `m ≥ 1`, `n ≥ 0`,
    with ratio `r = n/m` unique".
- **W2 (item 3, title and "Closed").** Item 3 excludes finite presentation of `E_(jN)(R)` only for `N ≥ 3`. Those are
  the ranks divisible by `j = md`.
  - The gate asks for `E_N(R)` finitely presented for **some** `N`. A rank `n` with `j ∤ n` is not excluded.
  - The symbol classes `{λ1_j, U}` live in `K_2(M_j(R)) ≅ K_2(R)`, but they are not symbols of units of `R`. So the
    gate's `K_2` half, which is phrased for symbols `{λ, x}` with `x ∈ R^x`, is not literally violated for `R`.
  - Either restrict the title and the Scope's "Closed" to "for all ranks divisible by `j`", or add a rank-transfer
    argument. Such an argument would need, for example, finite stable range of `R` itself. Attempt 12 shows gate
    hosts do not have it.
- **W3 (Examples, noncommutative bases).**
  - For `A_1(Q)` and `U(g)`, Weibel V.6.4 applies as pinned.
  - For their Ore localizations, the filtered theorem does not apply. The claim `K_0 = Z·[1]`, with `[1]` of infinite
    order, is still true, by a different argument:
    - the `G_0` localization sequence makes `K_0(A) → K_0(S^(-1)A)` onto, for `A` and `S^(-1)A` regular noetherian;
    - the rank over the Ore division ring of fractions shows `[1]` has infinite order.

    Give that argument, or restrict the examples.
  - Finite stable range of the localizations needs Stafford's bound, which is unread.

## Gate Attempt 12: the reading of `single-register-rings-divide-unit-at-finitely-many-primes` is correct

- **Part 2 is uniform in the type.** The statement already allows "finitely many state types".
  - In the proof, `G = ⊕_types LC(N ∪ ∞, Z)` is a finitely generated `Λ = Z[t]`-module.
  - A shift between any two types sends `[N=k]_τ` to `t^(k+a)[N=0]_(τ')`, so it is `Λ`-linear.
  - Resets contribute level-independent vectors.
  - Eventual constancy of availability gives the relation module `Λ t^K (t−1) e`, plus finitely many relations.
  - Top determination is never used.
  - So multi-type shift/reset designs are closed, with or without top determination, conditional on (P) or on the
    spine form with `δ_n ∈ B⁺`. Attempt 12 states that condition.
- **Dilation letters.** `N ↦ pN + r` is outside Part 2's hypotheses, so leaving those designs open is correct.
- **The finite-stable-range paragraph.** The argument is correct:
  - Vaserstein's `sr(M_n(R)) = ⌈(sr(R)−1)/n⌉ + 1` is unread, but standard.
  - Stable range `1` implies direct finiteness, and corners of directly finite rings are directly finite.
  - Gate hosts are not stably finite, so they have infinite stable range, and my Weibel III 5.5.2 route does not
    apply to them. Correctly recorded.
- **A stale note elsewhere (non-blocking).** The single-register node says the re-review of
  `register-completion-pimsner-from-supercoherence` by gq-referee-b is "pending". My re-review, with the
  point-indicator scope amendment, is 852a0771f. Only gq-referee-a's may still be outstanding.
