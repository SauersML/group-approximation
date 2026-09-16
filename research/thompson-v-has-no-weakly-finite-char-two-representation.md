---
rg: 2
id: thompson-v-has-no-weakly-finite-char-two-representation
kind: claim
title: Thompson's V has no nontrivial homomorphism into the unit group of a weakly finite ring of characteristic two
refuted_by:
  - thompson-v-is-f2-linear-sofic
  - thompson-v-modular-group-algebras-are-stably-finite
distinct_from:
  thompson-v-has-no-nontrivial-f2-rank-model: that excludes homomorphisms into characteristic-two rank ultraproducts; this excludes every weakly finite characteristic-two host, and rank ultraproducts are weakly finite, so this claim implies that one and the converse is not known.
  binary-complement-corner-has-no-weakly-finite-image: that is the Leavitt-unit form, equivalent to no weakly finite characteristic-two representation of L_(F_2)(1,2)^x; this is the same statement for the subgroup V, which implies it by simplicity of the Leavitt units.
  ternary-leavitt-units-have-no-weakly-finite-representation: that is the ternary form over F_3-algebras for the ternary Leavitt units; this is the binary form for V in characteristic two.
  thompson-v-modular-group-algebra-not-directly-finite: that asks for a one-sided unit in some F_p[V]; this asks that every weakly finite characteristic-two ring kill V, which forces F_2[V] and every F_2[Γ] with Γ containing V to be not directly finite.
artifacts:
  - research/artifacts/thompson-v-weakly-finite-representations-2026-09-16.md
---

**OPEN.** Let `W` be a unital ring with `2 · 1 = 0` that is weakly finite: `XY = I_n` implies `YX = I_n` for
square matrices of every size. Then every group homomorphism `V -> W^x` is trivial.

By Remark 2.1 of the artifact, "weakly finite" may be replaced by "directly finite" (the size-one condition)
without changing the claim. This equivalence is not formal: it runs through the order-three target and
Theorem B at the host `V`, that is, through both routes below.

**Equivalent to the order-three target** (artifact Theorem W_V, (a) <=> (d)):
`thompson-v-order-three-averaging-idempotent-is-full` holds iff this claim holds. The two directions are the
routes `thompson-v-averaging-fullness-from-no-weakly-finite-rep` and
`thompson-v-no-weakly-finite-rep-from-averaging-fullness`. The statement mentions no element of `V`, and by
artifact Corollary 3.1 it is also equivalent to fullness of `e_x` for any single `x` in `V` of order three.

**Consequences.**
- `thompson-v-has-no-nontrivial-f2-rank-model`, route `thompson-v-rank-gate-from-no-weakly-finite-rep`.
- The binary Leavitt-unit form: no nontrivial weakly finite characteristic-two representation of `R^x`
  (artifact Corollary 3.2(2)), and hence `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`.

**Refuted by** (artifact Section 5):
- `thompson-v-is-f2-linear-sofic`: a linear sofic approximation gives an injective homomorphism into a
  weakly finite characteristic-two rank ultraproduct;
- stable finiteness of `F_2[V]`, a case of `thompson-v-modular-group-algebras-are-stably-finite`: the
  inclusion `V -> F_2[V]^x` is then a nontrivial weakly finite representation;
- any group `Γ` containing `V` with `F_2[Γ]` directly finite, for the same reason.

## Attempts

- 2026-09-16 `swarm-thompson-v-order-three-averagi`: opened as the representation form of the order-three
  target (artifact Sections 2–5).
  - **Dead hosts** (artifact Corollary 3.4). No nontrivial homomorphism exists into a commutative ring, since
    `V` is perfect. None exists into a division ring of characteristic two, since `C_3²` cannot sit in the
    units of a finite field. None exists into any ring whose nilpotents have bounded index, which covers
    `M_n(D)`, reduced rings and finite-dimensional algebras: the `2^m`-cycles of `V` would become unipotent of
    bounded index. A refutation must use a noncommutative ring with nilpotents of unbounded index, such as
    a rank ultraproduct or a group algebra.
  - **The evaluation image.** For `P = π(F_2[V]) ⊆ L_(F_2)(1,2)`, `π(h) != 1`. So if `P` is directly finite,
    this claim is false. The Leavitt witness `b_0 = s0 + s10 + s11` for the binary corner has balanced row
    and column sums, so Lemma 3.1 of `research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md`
    does not separate it from `P`. It is not a sum of three elements of `V`. Where it stopped: whether
    `b_0 ∈ P`, and whether `P` is directly finite, are both open.
  - **Small supports** (artifact Proposition 4.1, from the computer-assisted Proposition 4.21 of
    arXiv:1112.1790). A witness `c e_h b = 1` has `|b|` and `|c|` odd and at least `3`, and never
    `(|c|, |b|) = (3, 3)`. If `|c| = 3`, then `|e_h b| >= 13`. Where it stopped: the next case needs
    direct-finiteness data at rank pairs `(3, 13)` and `(3, 15)`, which that paper does not cover.
