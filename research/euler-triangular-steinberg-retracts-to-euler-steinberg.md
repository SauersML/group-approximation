---
rg: 2
id: euler-triangular-steinberg-retracts-to-euler-steinberg
kind: claim
title: St_N(D) is a retract of St_N(T_l), so the triangular route needs the finite residual of St_N(D) to be finitely normally generated, and the known infinitely generated symbols of K_2(N, T_l) already live in St_N(D)
distinct_from:
  euler-triangular-steinberg-rf-residual-is-fng: that is the finite-residual question for St_N(T_l); this reduces its necessary part to the Euler ring D alone.
  steinberg-rf-forces-ring-rf: that says finite quotients of St_N(R) factor through St_N of finite quotient rings; this compares the finite quotients of St_N(T_l) with those of its retract St_N(D).
---

**ESTABLISHED** through `euler-triangular-steinberg-retracts-to-euler-steinberg-proof`. Refereed:
gq-referee-a PASS, proof-gap lens (report 06a8c773a); gq-referee-b PASS, citation and scope lens (report
9fd6ca4df, W1 and W2 applied). Elementary; no unread citation.

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
4. **Reading.** The symbols `{π_0, π_q}` that make `K_2(N, T_l)` infinitely generated
   (`euler-ring-rational-symbols-are-infinitely-generated`, which refutes
   `euler-triangular-ring-has-fg-central-unstable-k2`) lie in `St(ι)(St_N(D))`. For these symbols the module `M`,
   and with it `Z_(l)`, does not enter the question of whether they survive in finite quotients. This covers only
   the necessary direction of items 2--3: `K_2(N, T_l)` may also have classes involving `M` (gq-referee-b, W2).
   The corner symbols of `resolvent-ring-corner-symbols-survive-in-k2` are `K_2(Z_(l))` symbols of `e R_l e`, not
   `D`-symbols (gq-referee-b, W1).
