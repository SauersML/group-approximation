---
rg: 2
id: rf-resolvent-elementary-group-is-fp
kind: claim
title: For some prime l and some N >= 3, the elementary group E_N(R̄_l) over the residually finite resolvent ring is finitely presented
distinct_from:
  sl-n-z-localized-embeds-in-fg-rf-elementary-group: that establishes E_N(R̄_l) finitely generated and residually finite with SL_n(Z_(l)) inside; this asks for a finite presentation.
  z-localized-embeds-in-fp-rf-group: that asks for any finitely presented residually finite group containing Z_(l); this is one explicit candidate for it.
  leavitt-pairs-embed-sl-n-q-in-steinberg-groups: that works with Steinberg groups over rings with Leavitt pairs, which are never residually finite; this concerns the elementary group of a residually finite ring.
---

**OPEN.** There are a prime `l` and `N >= 3` such that `E_N(R̄_l)` is finitely
presented. Here `R̄_l` is the ring of `rf-resolvent-ring-has-z-localized-corner`.

**Use.** With `sl-n-z-localized-embeds-in-fg-rf-elementary-group` this gives
`z-localized-embeds-in-fp-rf-group`, by route
`z-localized-fp-rf-via-fp-resolvent-elementary-group`. For `N >= 6` it gives a
finitely presented residually finite group containing `GL_3(Z_(l))`, so containing
every `GL_3(Z[1/P])` with `l ∉ P`.

**Sub-questions, each falsifiable.**
1. **Is the presentation faithful?** `R̄_l` is a quotient of the finitely presented
   ring `R_l = Z<u, x, x', B, e | x x' = x' x = 1, x u = (u+l) x, B(u+1) = (u+1)B = 1,
   u e = e u = 0, e^2 = e>`. Is `R_l -> R̄_l` injective, i.e. is `R_l` residually
   finite? Two consistency checks pass. Relations derivable in `R_l` hold in every
   `M_r`: for example, `B e = e` and `k l · e x^k e = 0` follow from `ue = eu = 0` and
   `x u = (u+l)x`, and in `M_r` the element `e x^k e` is nonzero exactly when
   `l^(r-1)` divides `k`.
2. **Word problem.** Is the word problem of `R̄_l` decidable? A word vanishes iff it
   vanishes in every `End(M_r)`, and no uniform bound on `r` is known. Decidability is
   necessary for the claim, because finitely generated subgroups of finitely
   presented residually finite groups have solvable word problem.
3. **Steinberg and K_2.** If `R_l` is residually finite, is `K_2(N, R_l)` finitely
   normally generated in `St_N(R_l)`, and is `St_N(R_l)` finitely presented? That
   would present `E_N(R_l)`.

## Attempts

1. **Sub-question 1 fails (2026-09-17, lane gq-infinite-primes).** `R_l -> R̄_l` is not injective: `e x e - e x^q e`
   (`q != l` prime) is nonzero in `R_l` and zero in `R̄_l`
   (`resolvent-ring-presentation-is-not-faithful-on-r-bar`). Whether `R̄_l` has some other finite presentation
   is unknown, and `E_N(R̄_l)` is no longer the natural candidate.
   - The finitely presented object is `St_N(R_l)`, `N >= 4`, which contains `Z_(l)`
     (`z-localized-embeds-in-fp-kazhdan-steinberg-group`).
   - Sub-question 2 moves to the ring `R_l` (`resolvent-presentation-ring-is-residually-finite`: residually
     finite would give a decidable word problem).
   - Sub-question 3 becomes: is the kernel of `St_N(R_l) -> E_N(R_l)` detected in finite quotients
     (`resolvent-steinberg-group-is-residually-finite`)?
   This claim stays OPEN but is superseded as the main target.
