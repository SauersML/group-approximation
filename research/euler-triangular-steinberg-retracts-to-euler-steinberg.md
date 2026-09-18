---
rg: 2
id: euler-triangular-steinberg-retracts-to-euler-steinberg
kind: claim
title: St_N(D) is a retract of St_N(T_l), so the triangular route needs the finite residual of St_N(D) to be finitely normally generated, and the Euler base plays no role in the K_2 question
distinct_from:
  euler-triangular-steinberg-rf-residual-is-fng: that is the finite-residual question for St_N(T_l); this reduces its necessary part to the Euler ring D alone.
  steinberg-rf-forces-ring-rf: that says finite quotients of St_N(R) factor through St_N of finite quotient rings; this compares the finite quotients of St_N(T_l) with those of its retract St_N(D).
---

**ESTABLISHED** through `euler-triangular-steinberg-retracts-to-euler-steinberg-proof`. Lane proof, not
independently reviewed. Elementary; no unread citation.

**Notation.**
- `D` is the Euler ring (the skew Laurent ring of `resolvent-ring-has-path-normal-form`).
- `T_l = [[D, M],[0, Z]]` (`euler-triangular-ring-is-fp-rf`).
- `π : T_l -> D`, `[[d, n],[0, k]] -> d`, is the unital projection.
- `ι : D -> T_l`, `d -> [[d, 0],[0, 0]]`, is the non-unital corner inclusion.
- For a group `G`, `G_rf` denotes its finite residual.

**Statement.** Let `N >= 3`.
1. **Retract.** `St(ι) : St_N(D) -> St_N(T_l)` is injective, and `St(π) ∘ St(ι) = id`. It maps
   `K_2(N, D)` into `K_2(N, T_l)`.
2. **Same detection.** An element of `St_N(D)` survives in some finite quotient of `St_N(T_l)` iff it
   survives in some finite quotient of `St_N(D)`. Hence `St_N(T_l)_rf ∩ St(ι)(St_N(D)) = St(ι)(St_N(D)_rf)`.
3. **Necessity for the route.** Let `N >= 5`. If `St_N(T_l)_rf` is finitely normally generated, then so is
   `St_N(D)_rf`. That is,
   `euler-triangular-steinberg-rf-residual-is-fng` implies `euler-ring-steinberg-rf-residual-is-fng`.
4. **Reading.** The symbols that make `K_2(N, T_l)` infinitely generated
   (`resolvent-ring-corner-symbols-survive-in-k2` for `R_l`; gq-k2-q's refutation of
   `euler-triangular-ring-has-fg-central-unstable-k2` for `T_l`) lie in `St_N(D)`. The module `M`, and with
   it `Z_(l)`, does not enter the question of whether they survive in finite quotients.
