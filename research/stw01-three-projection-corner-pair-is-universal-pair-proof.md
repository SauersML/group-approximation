---
rg: 2
id: stw01-three-projection-corner-pair-is-universal-pair-proof
kind: route
title: Dilate every Hilbert-space pair of positive contractions into the corner of a representation of P_3
target: stw01-three-projection-corner-pair-is-universal-pair
requires: []
---

Full proof: §1 and §2 of
`research/artifacts/stw01-three-projection-corner-pair-test-2026-09-16.md`.

1. **Existence and surjectivity.** `h_2 = (r_2 r_1)^*(r_2 r_1)` and `h_3` are positive
   contractions in the unital C*-algebra `r_1 P_3 r_1`, whose unit is `r_1`. The universal
   property of `V` gives a unital *-homomorphism `psi : V -> C`, `h_0 -> h_2`, `k_0 -> h_3`, and
   its image is `C = C*(r_1, h_2, h_3)`.
2. **Corner dilation.** Let `a, b in B(H)` with `0 <= a, b <= 1`. Put
   `v_a = (a^(1/2), (1 - a)^(1/2))^T` and `v_b = (b^(1/2), (1 - b)^(1/2))^T`. Since `a` commutes
   with `1 - a`, `v_a^* v_a = 1`, and likewise for `b`. So `P_1 = 1 (+) 0`, `P_2 = v_a v_a^*` and
   `P_3 = v_b v_b^*` are projections in `M_2(B(H))`, with `P_1 P_2 P_1 = a (+) 0` and
   `P_1 P_3 P_1 = b (+) 0`, read off the `(1,1)` entries.
3. **Norm bound.** The universal property of `P_3` gives a unital *-homomorphism
   `pi : P_3 -> M_2(B(H))` with `r_j -> P_j`. Then `pi(r_1) = 1 (+) 0`, `pi(h_2) = a (+) 0` and
   `pi(h_3) = b (+) 0`. So for every noncommutative *-polynomial `P`, with its constant term read as
   a multiple of `r_1`, `pi(P(h_2, h_3)) = P(a, b) (+) 0`, and `||P(a, b)|| <= ||P(h_2, h_3)||_(P_3)`.
4. **Isometry.** The norm of `P(h_0, k_0)` in `V` is the supremum of `||P(a, b)||` over all
   Hilbert-space pairs of positive contractions. So
   `||P(h_0, k_0)||_V <= ||psi(P(h_0, k_0))|| <= ||P(h_0, k_0)||_V`. Thus `psi` is isometric on a
   dense *-subalgebra, hence isometric, injective, and an isomorphism onto `C`.

**Trust boundary.** The inputs are:
- the universal properties of `V` and of the unital full free product `P_3`;
- the fact that the norm of a universal C*-algebra is the supremum over Hilbert-space
  representations of its relations (Gelfand–Naimark);
- the continuous functional calculus for the square roots.

No quasitrace facts and no literature beyond these standard facts are used. The consequence on
the claim, non-exactness, is not part of this route.
