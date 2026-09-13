---
rg: 2
id: twisted-rope-trick-embeds-g-in-a-finitely-presented-group
kind: claim
title: "Higman's rope trick works with two different embeddings of the double"
---

Let `F` be free on `x_1, …, x_k`, let `R` be a normal subgroup of `F`, and let
`G = F/R`. Let `F_1, F_2` be copies of `F` with generators `x_i^(1)`,
`x_i^(2)`, and let `L = F_1 *_R F_2` be the double: the quotient of `F_1 * F_2`
by `r^(1) = r^(2)` for `r ∈ R`. Let `π: L → G` kill `F_2` and send `x_i^(1)` to
`x_i R`.

Let `ι, ι': L → P` be two injective homomorphisms into a group `P`. Write
`Hig_{ι,ι'}(G)` for the HNN extension of `P × G` conjugating `ι × 1` to
`ι' × π`: stable letter `t`, relations `t (ι(y), 1) t^{-1} = (ι'(y), π(y))` for
`y ∈ L`. Both associated maps are injective because `ι` and `ι'` are.

1. `G` embeds in `Hig_{ι,ι'}(G)`, as a factor of the vertex group.
2. If `P = ⟨S | Q⟩`, choose words `u_i, v_i, u'_i, v'_i` in `S` representing
   `ι(x_i^(1)), ι(x_i^(2)), ι'(x_i^(1)), ι'(x_i^(2))`. Then

       Hig_{ι,ι'}(G) = ⟨ S, x_1, …, x_k, t | Q, [s, x_i] (s ∈ S),
                         t u_i t^{-1} = u'_i x_i,  t v_i t^{-1} = v'_i  (1 ≤ i ≤ k) ⟩.

   In particular, if `P` is finitely presented then `Hig_{ι,ι'}(G)` is
   finitely presented.

For `ι' = ι` this is the rope trick of Definition 1.5 and Lemma 1.6 in
Fournier-Facio–Zaremsky, arXiv:2607.21727v1.

What the extra freedom buys:
- `ι'` may land in a part of `P` that `ι` avoids, so `H_2(ι) − H_2(ι')` need
  not vanish. It does vanish in Theorem B of the source, and that vanishing
  drives Theorem B.
- The obstruction that survives is recorded in
  `twisted-rope-trick-container-is-not-fp3-over-fp2-hosts`.
- The derivation only uses the finitely many relations of `P` that force
  `ι(r^(1)) = ι(r^(2))` and `ι'(r^(1)) = ι'(r^(2))`. So the finite
  presentation can survive for some infinitely presented `P`. The
  acyclic-host container, lane z1-01-ffz-fp3, is such a case.
