---
rg: 2
id: o2-suspension-central-unitary-evades-commutant-corners-proof
kind: route
title: AF-embed the O_2-suspension by Gabe, push the unitization into a corona by Arveson, and kill every corner trace with the Cuntz relation
target: o2-suspension-central-unitary-evades-commutant-corners
requires:
  - gabe-no-compact-open-prim-embeds-in-cone
---

Notation is as in the target. `J = C_0((0,1), O_2)`, `C = J + C·1`, and
`u = e^{2 pi i t} ⊗ 1`.

**Step 1 (the mark).**  `u` is a scalar-valued function times `1`, so it
commutes with `J` and with `1`. Hence `u` is central in `C`. We have
`u - 1 = (e^{2 pi i t} - 1) ⊗ 1 ∈ J`. The Gelfand spectrum of `C*(u, 1)` is
the one-point compactification of `(0,1)`, so `sp(u)` is the closure of
`{e^{2 pi i t} : 0 < t < 1}`, which is `T`. Also
`‖u - 1‖ = sup_t |e^{2 pi i t} - 1| = 2`.

**Step 2 (J is AF-embeddable).**  `J` is separable. It is nuclear, because
`O_2` and `C_0(0,1)` are, so it is exact. `O_2` is simple, so
`Prim J ≅ (0,1)`. Suppose `K` is a nonempty compact open subset of `(0,1)`.
It is closed, because `(0,1)` is Hausdorff, so it is clopen. Then
`K = (0,1)` by connectedness, which contradicts compactness. So `Prim J` has
no nonempty compact open subset. By Gabe's Corollary B (item 2 of
[[gabe-no-compact-open-prim-embeds-in-cone]]), there is an injective
*-homomorphism `J -> A` with `A` AF.

Independent check: `J` sits inside the cone `C_0((0,1], O_2)`. Cones are
quasidiagonal by Voiculescu's homotopy invariance. That route gives Step 3
through ucp maps as well.

**Step 3 (unital isometric embedding of C into a matrix corona).**

*Construction.*  Let `A~ = A + C·1` be the unitization of `A`, with a unit
adjoined even if `A` is unital. The map `j + mu ↦ j + mu 1` embeds `C`
unitally in `A~`. It is injective because `1 ∉ A`. Take a dense sequence
`(a_m)` in `C`. `A` is locally finite-dimensional, so for each `k` there is
a finite-dimensional C\*-subalgebra `F_k ⊆ A` with `dist(a_m, F_k + C·1) < 1/k`
for `m <= k`. Put `A_k = F_k + C·1`. This is a finite-dimensional unital
C\*-subalgebra of `A~`. Represent it unitally as `A_k ⊆ M_(d_k)`. By
Arveson's extension theorem, the inclusion `A_k -> M_(d_k)` extends to a ucp
map `E_k : A~ -> M_(d_k)`.

*Estimates.*  Let `a, a' ∈ A~` and `b, b' ∈ A_k` with `‖a - b‖, ‖a' - b'‖ <= eta`.
Write `R = max(‖a‖, ‖a'‖) + 1` and take `eta <= 1`. Since `E_k` is
contractive and `E_k(b) = b`,

    ‖E_k(a) - b‖ <= eta,
    ‖E_k(a a') - E_k(a) E_k(a')‖ <= ‖aa' - bb'‖ + ‖bb' - E_k(a)E_k(a')‖ <= 4 R eta,
    ‖E_k(a)‖ >= ‖b‖ - eta >= ‖a‖ - 2 eta.

*Limits.*  Since `dist(a_m, A_k) -> 0` for each `m`, we get
`‖E_k(a_m a_m') - E_k(a_m)E_k(a_m')‖ -> 0` and `‖E_k(a_m)‖ -> ‖a_m‖`.
These extend to all of `C` by density, because the maps are contractive.
So `iota(a) = [ (E_k(a))_k ]` is a unital *-homomorphism
`C -> Q = prod_k M_(d_k) / (+)_k M_(d_k)`. It is linear, `*`-preserving and
unital because each `E_k` is ucp, and multiplicative modulo `(+)_k M_(d_k)`.
The corona norm is `limsup_k`, so `‖iota(a)‖ = lim_k ‖E_k(a)‖ = ‖a‖`. Hence
`iota` is isometric.

**Step 4 (tracial states of C vanish on J).**  Let `sigma` be a tracial
state of `C`. Fix `f >= 0` in `C_0(0,1)` and write `f = g^2` with `g >= 0`
in `C_0(0,1)`. Define `phi(a) = sigma(f ⊗ a)` on `O_2`.

- `phi` is positive: `f ⊗ a* a = (g ⊗ a)^*(g ⊗ a)`.
- `phi` is tracial:
  `phi(ab) = sigma((g ⊗ a)(g ⊗ b)) = sigma((g ⊗ b)(g ⊗ a)) = phi(ba)`.

Let `s_1, s_2` be the Cuntz isometries. Then

    phi(1) = phi(s_1 s_1^* + s_2 s_2^*) = phi(s_1^* s_1) + phi(s_2^* s_2) = 2 phi(1),

so `phi(1) = 0`. A positive functional has `|phi(a)| <= ‖a‖ phi(1) = 0`, so
`phi = 0`. Every element of `C_0(0,1)` is a combination of four positive
ones, so `sigma(f ⊗ a) = 0` for all `f ∈ C_0(0,1)` and `a ∈ O_2`. The span
of these elementary tensors is dense in `J` and `sigma` is continuous. So
`sigma|_J = 0`.

**Step 5 (every commutant corner trace misses the mark).**  Let `H`, `Theta`,
`eps = u` and `B = iota(C)' ∩ Q` be as in the target. `H` generates `C` and
`iota` is continuous, so `Theta(H)' ∩ Q = iota(C)' ∩ Q`.

Let `q ∈ B` be a nonzero projection and `tau` a tracial state of `qQq`.

*Tracial states exist.*  Lift `q` to projections `q_k` of rank `r_k`. Then
`qQq ≅ prod_(k : r_k > 0) M_(r_k) / (+)`. For a free ultrafilter on the
infinite set `{k : r_k > 0}`, `lim tr_(r_k)` is a tracial state.

*The corner map is a *-homomorphism.*  `q` commutes with `iota(C)`, so
`c ↦ q iota(c)` is a unital *-homomorphism `C -> qQq`:

    q iota(c) q iota(c') = q^2 iota(c) iota(c') = q iota(cc').

Hence `sigma = tau(q iota(·))` is a tracial state of `C`.

*The trace misses the mark.*  By Step 4, `sigma(|u - 1|^2) = 0`, since
`|u - 1|^2 ∈ J`. So

    ‖q Theta(eps) q - q‖_(2,tau)^2 = tau(q iota(|u - 1|^2)) = sigma(|u - 1|^2) = 0.

The first equality uses `q iota(u - 1) q = q iota(u - 1)`.

**Step 6 (no approximate eigencorner).**  For `lambda ∈ C`, `q` and `tau` as
above, write `Theta(eps) - lambda = (Theta(eps) - 1) + (1 - lambda)`. Since
`‖x‖_(2,tau) <= ‖x‖` and `‖q‖_(2,tau) = 1`,

    ‖(Theta(eps) - lambda) q‖ >= ‖(Theta(eps) - lambda) q‖_(2,tau)
                              >= |1 - lambda| - ‖(Theta(eps) - 1) q‖_(2,tau)
                               = |1 - lambda|.

This uses `‖(Theta(eps) - 1) q‖_(2,tau)^2 = tau(q iota(|u - 1|^2) q) = 0`.

**Step 7 (nontriviality).**  `iota` is isometric, so
`‖Theta(eps) - 1‖ = ‖u - 1‖ = 2`.

Steps 5 and 7 contradict `commutant-projection-extraction`. Steps 6 and 7
contradict its contrapositive for every `delta ∈ (0, 2]`. ∎
