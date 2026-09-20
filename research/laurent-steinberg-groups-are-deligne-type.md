---
rg: 2
id: laurent-steinberg-groups-are-deligne-type
kind: claim
title: For q >= 3 and n >= 3, St_n(F_q[t,t^-1]) is a finitely generated Kazhdan group whose tame symbol {t,a} is a central element of order q-1 lying in every finite-index subgroup; for q odd it is of Deligne-type
distinct_from:
  resolvent-steinberg-rf-residual-is-finitely-normally-generated: that concerns corner symbols in a noncommutative resolvent ring over Z; this is the one-variable Laurent ring over a finite field, where the invisible part is a single explicit cyclic group of symbols.
  laurent-unstable-k2-splits-by-tame-symbol: that computes K_2(n, k[X,X^-1]); this uses it to show the symbol {t,a} dies in every finite quotient, so the Steinberg group is not residually finite.
  steinberg-rf-forces-ring-rf: that reduces finite quotients of St_N(R) to finite quotient rings; this applies it to kill one explicit central element.
---

**ESTABLISHED** (proof route `laurent-steinberg-deligne-type-proof`).

Let `q >= 3` be a prime power of characteristic `p`, `R = F_q[t,t^-1]`, `n >= 3`, `a` a generator
of `F_q^×`, `α` a fixed root, and

```text
c = {t, a}_α  in  St_n(R).
```

1. `c` is central in `St_n(R)`, lies in `K_2(n,R)`, and has order exactly `q - 1`. In particular
   `c ≠ 1`.
2. `c` lies in every finite-index normal subgroup of `St_n(R)`. So `St_n(R)` is not residually
   finite.
3. `St_n(R)` is finitely generated and has property (T).
4. For `q` odd, `J = c^((q-1)/2)` is a central element of order two in `ker_RF`. So `St_n(R)` is
   of Deligne-type in the sense of `bdl-deligne-type-two-norm-inapproximability`, for every odd
   `q` and every `n >= 3`.
5. `K_2(n,R) = ⟨c⟩ ≅ Z/(q-1)`, and `ker_RF = K_2(n,R)`. So `St_n(R)` is a central extension of
   the linear S-arithmetic group `E_n(R) = St_n(R)/K_2(n,R)` by a cyclic group of order `q - 1`,
   and every finite quotient of `St_n(R)` factors through `E_n(R)`. This is the
   positive-characteristic analogue of Deligne's cover of `Sp_(2g)(Z)`.

**Consequence.** With `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, `St_n(R)` is
either not flexibly HS stable or not hyperlinear. With `bdl-deligne-type-two-norm-inapproximability`
(Theorem 1.3, `q` odd), it is either not `||.||_2`-stable or not `||.||_2`-approximated.

Characteristic `2` with `q = 2` is excluded, since `F_2^× = 1` and there is no symbol. This is
consistent with `sl3-laurent-f2-is-flexibly-hs-stable`.
