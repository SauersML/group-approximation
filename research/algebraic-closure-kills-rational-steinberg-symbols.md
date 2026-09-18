---
rg: 2
id: algebraic-closure-kills-rational-steinberg-symbols
kind: claim
title: If the algebraic closure of Q embeds unitally in a ring R, every rational Steinberg symbol is trivial in St_N(R) for N >= 3, so the rational K_2 budget by itself obstructs no ring containing it, such as R_L
distinct_from:
  matricial-divisibility-kills-rational-k2-symbols: that kills K_2(Q) in the stable K_2(R) when R ≅ M_n(R_n) for n divisible by every integer, which forces [1] to be divisible in K_0; this kills it in St_N(R) itself for each N >= 3 when a field such as the algebraic closure of Q embeds, with no condition on K_0.
  full-corners-must-kill-rational-k2-symbols: that is the necessary condition (finitely presented E_N(R) forces a finite rational image in every full corner); this is a sufficient condition that meets it.
  infinitely-generated-symbols-block-fp-elementary-groups: that turns an infinitely generated symbol group into an obstruction; this shows the rational part of that group is trivial in every ring containing the algebraic closure.
---

**ESTABLISHED** through `algebraic-closure-kills-rational-steinberg-symbols-proof`. Lane proof, not independently
reviewed. The inputs are cited theorems on `K_2` of fields (Tate, Suslin, and injective stability for fields); the
argument is two lines. No priority is claimed.

**Statement.** Let `R` be a unital ring with a unital ring homomorphism `Q -> R`, and `N >= 3`.
1. **Fields that kill `K_2(Q)`.** Suppose `Q -> R` extends to a unital ring homomorphism `F -> R`, where `F ⊇ Q` is
   a field and `K_2(Q) -> K_2(F)` is zero. Then the image of `K_2(N, Q)` in `St_N(R)` is trivial. In particular
   every rational Steinberg symbol `{λ, μ}_N`, with `λ, μ in Q^x`, is `1` in `St_N(R)`. No stability, centrality
   or finiteness hypothesis on `R` is used.
2. **The algebraic closure is such a field.** `F = Q̄`, and every field containing it, satisfies item 1:
   `K_2(Q)` is a torsion group (Tate), and `K_2(Q̄)` is torsion-free (Suslin).
3. **The literal symbol budget fails.** `R_L` is finitely presented over `Z` and simple
   (`leavitt-resolvent-ring-is-fp-simple-of-char-zero`), and `Q̄` embeds in it unitally
   (`field-envelopes-pass-to-algebraic-closures`, item 2). So all of `K_2(N, Q)` dies in `St_N(R_L)` for every
   `N >= 3`. Hence no statement of the form "every finitely presented ring containing `Q` has an infinitely
   generated rational part of `K_2(N, R)`, even modulo finite normal generation" is true. The same holds for
   `S ⊗_Q L_Q(1,2)`, for every `Q`-algebra `S`.
4. **Central algebraic closure.** Suppose `Q̄ ⊆ Z(R)`. For `λ in Q̄^x` and `x in R^x`, the symbol `{λ, x}` in
   `K_2(R)` is divisible by every integer `m`: `{λ, x} = m {ν, x}` for any `ν in Q̄` with `ν^m = λ`. So if `E_N(R)`
   is finitely presented for some `N >= 3`, every such symbol is `0` in `K_2(R)`.

## Consequences for the gate `fp-simple-resolvent-ring-with-divisible-unit-class`

- **Item 5, rational half, for free.** A candidate ring containing `Q̄` unitally has trivial rational symbols in
  every `St_N(R)`, `N >= 3`, not only in the stable `K_2(R)`. So matricial divisibility (items 3 and 4 of the gate) is
  not needed for this purpose. The gate still needs `[1]` of infinite order for `K_1` detection
  (`rational-k1-detection-forces-infinite-order-unit-class`), and still needs control of the symbols `{λ, x}` for
  non-rational units `x` (`resolvent-register-units-give-rational-symbols`). By item 4, when `Q̄` is central those
  symbols must vanish outright.
- **What a symbol-budget obstruction would have to say.** A version of the budget that still bites must exclude
  `Q̄`. For example: no finitely presented ring in which `[1]` has infinite order contains `Q̄` unitally. That is
  not known. `R_L` does not decide it, since its Leavitt `(1,2)`-tuple gives `[1] = 0`.
- **Unitality matters.** Item 1 needs `F -> R` to extend the given `Q -> R`. For a corner `eRe` with the map
  `q -> qe`, a copy of `Q̄` in `R` helps only if it commutes with `e`.
