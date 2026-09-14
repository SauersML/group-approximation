---
rg: 2
id: brin-thompson-2v-order-three-averaging-idempotent-is-full
kind: claim
title: The averaging idempotent of an order-three element of V is full in the binary group algebra of the Brin–Thompson group 2V
distinct_from:
  thompson-v-order-three-averaging-idempotent-is-full: that asks for b and c inside F_2[V]; this allows them in the larger algebra F_2[2V], so that claim implies this one.
  binary-cyclic-averaging-idempotent-is-full-on-leavitt-units: that asks for the solution over the units of L_(F_2)(1,2); this asks for it over 2V, which sits in the units of L_(F_2)(1,2) ⊗ L_(F_2)(1,2).
artifacts:
  - research/artifacts/brin-thompson-2v-gottschalk-host-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`, `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1`, with dual `t_i`, and
`g = s_2 t_1 + s_3 t_2 + s_1 t_3` in `V`. Embed `V` in `2V` along the first coordinate (`x -> x ⊗ 1`), and put
`e = 1 + [g ⊗ 1] + [g² ⊗ 1]` in `F_2[2V]`. There are `b, c` in `F_2[2V]` with `c e b = 1`.

Equivalently, with `T = (1 - e) F_2[2V] (1 - e)`, the pair `(K_0(T), [T])` admits no state. This is the binary
Theorem B for the `D`-stable host `2V` (artifact Proposition 2.1). Then `F_2[2V]` is not directly finite and
`2V` is not surjunctive (`brin-thompson-2v-nonsurjunctive-from-averaging-fullness`).

## Attempts
* **Finite-subgroup relations and the baker unit (w6-free-neg-d, 2026-09-12; artifact Propositions 2.4–2.5).**
  The baker unit `u = Σ_i s_i ⊗ t_i` makes the halving `D` inner on `V ⊗ 1` and turns the tower idempotents
  into external products. Write `e^(1) = e` and `e^(2) = u^(-1) e u = 1 + [1 ⊗ g] + [1 ⊗ g²]`, with complements
  `f^(i)`. A state of `K_0(F_2[2V])` then gives `e^(1) e^(2)`, `e^(1) f^(2)`, `f^(1) e^(2)`, `f^(1) f^(2)` the
  values `1 - 4b`, `b`, `b`, `2b` for one `b` in `[0, 1/4]`. The endpoints `b = 0` (augmentation) and `b = 2/9`
  (independent regular product) are both consistent with every relation coming from finite subgroups and `u`.
  Where it stopped: these relations do not decide whether `T` has a state.
