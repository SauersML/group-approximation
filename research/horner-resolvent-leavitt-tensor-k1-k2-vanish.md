---
rg: 2
id: horner-resolvent-leavitt-tensor-k1-k2-vanish
kind: claim
title: For the Horner-resolvent algebra R_2 over F_2, the Leavitt tensor R_2 ⊗ L_(F_2)(1,2) has K_1 = K_2 = 0
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that gives K_*(L_2 ⊗ R) = 0 for regular supercoherent R; this asks it for one explicit R, the Horner-resolvent completion, which is not known to be regular supercoherent.
  leavitt-tensor-powers-have-trivial-k-theory: that is the same vanishing for tensor powers of L; this is for a Leavitt--Nekrashevych completion of a commutative regular ring with one non-flat reset letter.
  leavitt-resolvent-k-theory-is-shifted-rational-k-theory: that computes K_*(R_L) itself in characteristic zero, and it is nonzero; this asks for the K-theory of the Leavitt tensor in characteristic two, where the expected answer is zero.
---

**OPEN.** Let `R_2` be the algebra of `char-p-rational-function-field-in-fp-simple-algebra`
with `p = 2`, and `L = L_(F_2)(1,2)`. Then `K_1(R_2 ⊗ L) = K_2(R_2 ⊗ L) = 0`.

**Why it matters.** It is the only open input of `gl-n-f2t-bh-via-horner-resolvent-leavitt-tensor`,
which then puts every `GL_n(F_2(t))`, all `n` at once, in one finitely presented simple group
`(R_2 ⊗ L)^x`. Finite normal generation of `ker(St_n(R_2 ⊗ L) -> E_n(R_2 ⊗ L))` for one `n >= 4`
would also do, through `leavitt-tensor-elementary-host-criterion` applied to
`B = M_(n+1)(R_2)` and the perfect group `SL_(n+1)(F_2(t)) ⊇ GL_n(F_2(t))`.

**Sufficient conditions.**
1. `R_2` is regular supercoherent: then `K_*(L ⊗ R_2) = 0` by Ara--Cortiñas Proposition 6.2
   (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).
2. A Pimsner-type long exact sequence for `R_2 ⊗ L`, viewed as the Leavitt--Nekrashevych
   completion of `B ⊗ L` along `ψ ⊗ id` (the covariance `ℓ = Σ_x s_x ℓ t_x` makes the two
   presentations agree), with coefficients whose own `K`-theory vanishes. For the commutative
   base `B = S^(−1) F_2[t, P]`, which is regular noetherian, `K_*(B ⊗ L) = 0` by Proposition 6.2.

## Attempts
1. **The reset letter is not flat.** `σ_v : B -> B` (`P ↦ 1`) makes `B` a module over itself
   through `F_2[t,P] -> F_2[t]`, which is not flat. So the core `colim M_(d^n)(B)` along `ψ` is a
   colimit along non-flat maps, and regular coherence of the core does not follow from that of `B`.
   This is the same obstacle as for the characteristic-zero resolvent ring `R_L`, where
   `register-completion-pimsner-from-supercoherence` removes it by enlarging the coefficients with
   point indicators. That node covers one register over `Q` with letters
   `N ↦ N + a`, `N ↦ pN + r`, `N ↦ c`. Here there are two registers and the letter `t ↦ t^2`.
   Adapting it is the natural route.
2. **Expected answer.** In characteristic zero the Pimsner sequence gave
   `K_n(R_L) ≅ K_(n−1)(Q)`: the cokernel of `1 − [X]` comes from the reset letter. Tensoring with
   `L`, where `[1] = 2[1]`, should kill every such class, as `1 − 2 = −1` does for `L` itself.
   This is a heuristic, not a proof.
3. **KH vanishes unconditionally; the gate is a regularity question** (2026-09-18, lane `bh-algebra`).
   - ABC (arXiv:0903.0056v2, read from the MSI text), (8.8): `KH(A ⊗ L_(1,n)) = KH(A; Z/n)`
     for every ring `A`, where `L_(1,1) = L(1,2)`. With `n = 1`, `KH_*(R_2 ⊗ L) = 0`, and
     likewise `KH_*(R_2[x_1..x_p] ⊗ L) = 0`, with no hypothesis on `R_2`.
   - ABC §8 (citing Weibel): if a unital ring is `K_n`-regular, then `K_m = KH_m` for `m <= n`.
     So the gate holds as soon as `R_2 ⊗ L` is `K_2`-regular.
   - If `R_2` is regular supercoherent, so is every `R_2[x_1..x_p]` (ABC §7, via Vogel regularity).
     Then Proposition 6.2 gives `K(R_2[x..] ⊗ L) = 0` for all `p`: `R_2 ⊗ L` is `K`-regular with
     trivial `K`-theory. So the gate follows from regular supercoherence of `R_2` alone.
4. **Removing the non-flat reset by point indicators (sketch, not a proof).** In `R_2` the vacuum
   projections `e_u = s_u s_v t_v t_u` (`u` a Horner word) are orthogonal, commute with `t` and
   `P`, and satisfy `P e_u = f_u(t) e_u`. The ring `B⁺ = B + Σ_u F_2(t) e_u` is `σ`-stable
   (`σ_(h_a)(e_(h_a u')) = e_(u')`, `σ_v(e_∅) = 1`, all other images `0`), and `R_2` is its
   Leavitt--Nekrashevych completion. It is an extension `0 -> ⊕_u F_2(t) -> B⁺ -> B -> 0`, the
   two-dimensional analogue of `eventually-rational-register-ring-is-regular-supercoherent`.
   - Its localizations are fields or localizations of `B`.
   - Generic freeness along the curves `P = f_u` looks enough for coherence, as in part 2 of
     that node.
   - `σ_v` becomes flat for the same reason as the reset there.
   If this is written out, the core of `R_2` is regular supercoherent and `(P)` holds for `R_2`
   (for example `K_0(R_2) = Z/3`, from `[1] = 4[1]` and `[e_u] = [1]`).
   - **What still fails.** Regular supercoherence of the core does not give it for `R_2` itself.
     ABC Theorem 3.6 with `A = L` leaves the twisted nil terms
     `NK((S ⊗ L)~; φ̂ ⊗ 1)_±`. Lemma 7.2 kills them only for a regular supercoherent ring with an
     automorphism, and `S ⊗ L` is not known to be one.
   - **The remaining gap, stated sharply.** A twisted form of Proposition 6.2: `K(D[t; α] ⊗ L) = 0`
     for regular supercoherent `D` and an automorphism `α`. Equivalently, regular supercoherence of
     twisted Laurent rings over `D`.
5. **Reduction to K-theory of the point-indicator base** (2026-09-18, lane `bh-algebra`). Two clean
   pieces, and one remaining check.
   - *(a) The vanishing is inherited from the base.* Let `B⁺_2` be the char-2 point-indicator base of
     Attempt 4 (the `σ`-closure of `t`, `P`, the reciprocal `Γ`, and the vacuum projections `e_u`), so
     that `R_2` is the register completion with base `B⁺_2`. Run ABC Theorem 3.6 (as in
     `register-completion-pimsner-from-supercoherence`) on `R_2 ⊗ L` over the coefficient ring
     `B⁺_2 ⊗ L`. Its spectrum is `hocofiber(1 − φ_* : K(B⁺_2 ⊗ L) -> K(B⁺_2 ⊗ L))` once the twisted `NK`
     terms vanish. So if `K_*(B⁺_2 ⊗ L) = 0`, then `K_*(R_2 ⊗ L) = 0`, and in particular `K_1 = K_2 = 0`.
   - *(b) `K_*(B⁺_2 ⊗ L) = 0` from regular supercoherence of `B⁺_2`.* By Ara--Cortiñas Proposition 6.2
     (`ara-cortinas-leavitt-tensor-k-theory-vanishes`), `K_*(L ⊗ R) = 0` for every regular supercoherent
     `R`. So this reduces to: `B⁺_2` is regular supercoherent.
   - *Remaining check.* `B⁺_2` is the two-variable analogue of
     `eventually-rational-register-ring-is-regular-supercoherent`: functions on the Horner tree valued in
     `F_2(t)`-tails, plus the resolvent along the curves `P = f_u(t)`. Over the field `F_2` the
     semihereditary argument (gcd in the PID of tails, splitting off a finitary corner) goes through for
     the `P`-direction; the extra variable `t` requires that the tail ring be a localization of
     `F_2[t]` closed under `t ↦ t^2`, which it is, and that generic freeness along the curves `P = f_u`
     hold, as in Part 2 of that node. Writing this out is the one open step; it is a regularity
     computation over `F_2`, with no `K`-theory left.
   - *(c) Twisted `NK` vanishing.* The same as in the char-0 node: the core `D ⊗ L` is a filtered colimit
     of regular supercoherent rings along flat maps, so ABC Lemma 7.2 kills `NK(D ⊗ L; φ̂ ⊗ 1)_±`. This
     uses regular supercoherence of `B⁺_2 ⊗ L`, which holds when `B⁺_2` is regular supercoherent, since
     `L` is (Ara--Cortiñas Lemma 6.1) and the relevant tensor is handled exactly as the base case there.
     [This step reuses the char-0 machinery verbatim once (b) is in hand.]
   So the whole gate reduces to regular supercoherence of the explicit commutative-plus-indicators ring
   `B⁺_2`, with no remaining `K`-theory.
6. **Crossed-product form and the exact tradeoff** (2026-09-18, lane `bh-algebra`).
   - `R_2` has `4 = 2^2` letters. By `leavitt-tensors-of-2-power-completions-are-z-crossed-products`,
     `R_2 ⊗ L = (R_(2,0) ⊗ L) ⋊_(Ad U) Z`. So `K(R_2 ⊗ L)` is the Bass--Heller--Swan cofibre of
     `1 − Ad U_*` on `K(R_(2,0) ⊗ L)`, plus the twisted Nil terms of `C = R_(2,0) ⊗ L`. Farrell--Jones
     for `Z` is automatic. What remains is `K(C) = 0` and Nil vanishing, by
     `regular-coherent-laurent-coefficients-kill-twisted-nil-terms`, once `C` and its Laurent
     extensions are regular coherent.
   - **Without point indicators the coefficient algebra is good.** For the presented base
     `B = S^(−1) F_2[t, P]`, `L ⊗ B` is a central localization of `L[t, P]`, and `L[t, P]` is regular
     supercoherent by Ara--Cortiñas Lemma 6.1 (polynomial extensions of `L`). So `L ⊗ B` is regular
     supercoherent, and `K(L ⊗ B) = 0`. But the core `colim M_(4^n)(B)` is taken along the non-flat
     reset `P ↦ 1`, so its coherence does not follow.
   - **With point indicators the colimit is good but the coefficients are not known to be.** Over
     `B⁺_2` every letter is flat (Attempt 4), so the core is a flat colimit. But regular coherence of
     `L ⊗ B⁺_2`, a Leavitt algebra over a non-noetherian fibre product of `B` with `⊕_u F_2(t)`, is not
     known. Its central localizations are `L_(F_2(t))(1,2)` or `L ⊗ B_q`, both regular supercoherent, but
     coherence of `L ⊗ B⁺_2` is not local.
   - **So the gate is exactly the reset tradeoff:** flatness of the reset needs point indicators, and
     point indicators cost the noetherian localization that makes `L ⊗ B` coherent. A proof needs a
     local-to-global coherence statement for `L ⊗ B⁺_2`, or a reset-free design that still makes
     every monic polynomial a value (the design in `char-p-rational-function-field-in-fp-simple-algebra`
     uses the reset essentially: without it only powers of `t` get inverted).
   - *Lesson for general BH.* In register (resolvent) hosts the reset letter is where both the
     field of constants and the `K`-theory difficulty come from. Every register host has this tradeoff,
     in characteristic zero too, where `register-completion-pimsner-from-supercoherence` pays with point
     indicators.
