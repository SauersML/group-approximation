---
rg: 2
id: jacobson-el3-lef-from-local-mirror-lifts
kind: claim
title: EL_n(J) is LEF as soon as the symbol inversion has partial lifts on every ball; a global lift is an injective endomorphism, and no global lift that is spatial on the finitary kernel exists for n >= 3, because the commuting-pair index changes sign under inversion
distinct_from:
  jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group: that writes EL_n(J) = P/L_- and, in (MQ4), embeds subgroups over which the mirror extension has a homomorphic section; this asks for partial sections of the whole group over balls, shows that they suffice for LEF, and rules out every global spatial section by an index invariant.
  binary-jacobson-el2-is-lef: that builds the global mirror lift psi = K tau(g)^(-t) K^(-1) at rank two; this shows that no analogue that is spatial on the finitary kernel exists at rank n >= 3, and identifies the invariant that vanishes at rank two and not at rank three.
  jacobson-symbol-sequence-does-not-virtually-split: that shows lifts of the commuting pair (x_12(a), h^k) never commute; this turns the same image layer into a signed invariant of the pair and shows that the symbol inversion reverses its sign.
  cohn-elementary-group-is-not-lef: that proves EL_n(J) is not LEF for n >= 4; here that is combined with (L1) to show that partial mirror lifts fail on an explicit finite ball at n = 4, so no mirror-lift construction can work uniformly in the rank.
---

**ESTABLISHED** (route `jacobson-el3-lef-from-local-mirror-lifts-proof`). Parts (L1)–(L3) are unconditional.
Part (L4) proves nonexistence under the stated spatiality hypothesis (S); nonexistence without (S) is **OPEN**.

**Notation** (as in `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`).
- `J = F_2<S,T | TS=1>` acts on `V_+ = F_2^(N)`; `A = F_2[z^(+-1)]`; `pi : J -> A`, `S -> z`, `T -> z^(-1)`.
- `E = E_n = EL_n(J) = GL_n(J)` acts on `V = V_+^n` with coordinates `V_1, ..., V_n`; `L = GL_fin(V) = ker pi`.
- `iota` is the ring automorphism `z -> z^(-1)` of `A`, applied entrywise to `SL_n(A)`. The mirror symbol is
  `pi_- = iota o pi` (there it is called `theta`).
- `V^*` is the restricted dual (span of the dual basis); `g` acts on it by `g^(-t)`.

**Definition.** A *partial iota-lift on* a finite set `B ⊆ E` containing `1` is a map `f : B·B -> E` with
`f(gh) = f(g) f(h)` for `g, h in B`, and `pi(f(g)) = iota(pi(g))` for `g in B`. A *global iota-lift* is a
homomorphism `f : E -> E` with `pi o f = iota o pi`. Rank two has one: `psi` of `binary-jacobson-el2-is-lef`.

**Theorem.**
- **(L1) Local criterion.** Suppose every finite `B ⊆ E_n` carries a partial iota-lift. Then `E_n` is LEF. Each
  map is `g -> (g, f(g))` into the LEF group `P` of (MQ2).
- **(L2) Rank four and up.**
  - For `n >= 4` there is no global iota-lift.
  - For `n = 4`, some explicit finite ball `B_4` of `E_4` carries no partial iota-lift. It is the ball containing
    the relators of a finite presentation of `St_4(J) = E_4`.
  - At `n = 3` the same conclusion holds if `E_3` is finitely presented (`binary-jacobson-el3-is-finitely-presented`).
- **(L3) The commuting-pair index.**
  - Let `u = x_12(a)`, with `a != 0`, and `g in SL_n(A)` commute. For lifts `u~`, `g~ in E`, the subspace
    `W = (u~+1)V` is commensurable with `g~ W`. The relative index `I(u,g) = [g~W : W]` depends only on `(u,g)`.
  - Two values: `I(x_12(a), h^k) = -k` for `h = diag(z, z, z^(-2), 1, ..., 1)`, and
    `I(x_12(a), iota(h^k)) = +k`.
  - The symbol inversion therefore sends a pair of index `-k` to a pair of index `+k`.
  - At `n = 2`, `I(x_12(a), g) = 0` for every `g` commuting with `x_12(a)`.
- **(L4) Global lifts.** Let `n >= 3` and let `f` be a global iota-lift.
  - (a) `f` is injective. So `E` embeds in itself with symbol inverted.
  - (b) `f` is not *spatial on `L`*. That is, it fails hypothesis (S) below.
  - **(S).** There is a linear isomorphism `Phi : V^(r_+) (+) (V^*)^(r_-) (+) V_0 -> V` such that, for
    `l in L`, `Phi^(-1) f(l) Phi = l^(+r_+) (+) (l^(-t))^(+r_-) (+) 1_(V_0)`. Here `r_+-` are finite and
    `V_0` has any dimension.
  - Hypothesis (S) holds for every lift assembled from conjugation by an invertible operator of `V`, the
    contragredient `g -> g^(-t)`, the anti-automorphism `tau : S <-> T`, and block sums of these. That covers
    every construction of the rank-two type.

**Impact for `binary-jacobson-el3-is-sofic`.**
- **The class killed.** "Prove EL_3(J) is LEF by a global mirror section of `P -> E`, as at rank two." Every
  spatial global section dies.
- **The invariant.** The commuting-pair index `I`. Natural and dual copies each carry `I` with multiplicity one,
  and the mirror section must carry `-I`.
- **Where every member dies.** The step `-(r_+ + r_-)k = +k`.
- **Survivors.** Precisely two:
  1. partial lifts that do not globalize, which are enough by (L1) and are consistent with `E_3` not finitely
     presented;
  2. global lifts whose `L`-module `V_f` is a non-split finitary extension. Such modules exist: for example
     `V + F_2 w` inside `F_2^N`, where `w` is not finitely supported.
- **What a rank-three LEF proof must do.** By (L2), a partial-lift construction must fail at `n = 4`. So it cannot
  work uniformly in `n`, and has to use `n = 3` itself, which is exactly where finite presentability is open. By
  (L4), it must build models not induced from one fixed operator picture of `L`.

DERIVATION
jacobson-el3-lef-from-local-mirror-lifts-proof
