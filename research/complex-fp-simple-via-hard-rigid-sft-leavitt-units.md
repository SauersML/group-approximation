---
rg: 2
id: complex-fp-simple-via-hard-rigid-sft-leavitt-units
kind: route
title: Take a hard quantum rigid free minimal Z^2-SFT; the units of its binary crossed product tensored with L_2 are finitely presented and simple, and their word problem decides the SFT language
target: fp-simple-groups-with-arbitrarily-complex-word-problem
requires:
  - hard-quantum-rigid-free-minimal-z2-sfts-exist
  - free-minimal-cantor-crossed-products-are-central-simple
  - cantor-crossed-product-leavitt-tensors-are-k-trivial
  - virtually-poly-z-groups-satisfy-fjc-with-additive-coefficients
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - central-simple-leavitt-tensor-unit-groups-are-simple
  - sft-leavitt-units-word-problem-computes-sft-language
---

Lane proof (swarm-0917-w18c-w18c-bh-pull, 2026-09-19). Not independently reviewed. **Conditional on the
imported criteria of Khanh arXiv:2609.08428v1**, through `leavitt-tensor-hosts-acyclic-steinberg-and-fp`
(finite presentation of the units). Every other premise is a literature import or a lane proof.

**How this differs from nearby routes.**
- `arbitrarily-complex-fp-simple-via-hard-minimal-sft-v-full-groups` also takes hardness from a free
  minimal `Z^2`-SFT, but needs finite presentation of alternating full groups of `V × (Z^2 ⋉ X)`, which is
  open. Here finite presentation comes from quantum rigidity (the SFT premise) and the Leavitt-tensor
  host theorems.
- `complex-fp-simple-groups-from-boone-higman` and its variants need a universality statement. This
  needs none.

## Proof

Fix a recursive `T`. Replacing `T` by `n ↦ max_(m <= n) T(m)` only strengthens the conclusion, so assume
`T` nondecreasing. Put `T'(n) = T(n^6) + n^6`, which is recursive and nondecreasing.

1. **The shift.** By `hard-quantum-rigid-free-minimal-z2-sfts-exist` applied to `T'`, choose a free
   minimal `Z^2`-SFT `Ω` with `B = LC(Ω, F_2) ⋊ Z^2` finitely presented as an `F_2`-algebra and `Ω` not
   `T'`-decidable. `Ω` is infinite (a finite minimal `Z^2`-system is a periodic orbit, not free), so it is
   a Cantor space. As `F_2` is finite, `B` is also finitely presented as a ring (add the relation `2 = 0`).
2. **`B` is central simple.** The action is free, hence topologically free, and minimal. By
   `free-minimal-cantor-crossed-products-are-central-simple`, `B` is simple with centre `F_2`.
3. **K-theory.** `Z^2` is torsion-free and satisfies the `K`-theoretic Farrell–Jones conjecture with
   additive coefficients (`virtually-poly-z-groups-satisfy-fjc-with-additive-coefficients`). By
   `cantor-crossed-product-leavitt-tensors-are-k-trivial`, `K_n(R) = 0` for all `n`, where
   `R = B ⊗ L_(F_2)(1,2)`.
4. **Finite presentation.** By item 3 of `leavitt-tensor-hosts-acyclic-steinberg-and-fp` (`B` simple,
   finitely presented, `K_1(R) = K_2(R) = 0`), `S = R^×` is finitely presented.
5. **Simplicity.** By item 2 of `central-simple-leavitt-tensor-unit-groups-are-simple`,
   `S ≅ GL_3(R) = E_3(R)` is simple, infinite and nonabelian.
6. **Hardness.** Suppose the word problem of `S`, for some finite generating set, is decidable in time
   `C·T(Cl) + Cl + C`. `S` is finitely generated and contains the subgroup `Q` of
   `sft-leavitt-units-word-problem-computes-sft-language` (item 1). By its item 3 with
   `W(l) = C·T(Cl) + Cl + C`, the globally admissible `n × n` patterns of `Ω` are decidable in time
   `C_1·(C·T(C C_1 n^5) + C C_1 n^5 + C) + C_1 n^6 + C_1`. For `n >= C C_1`, `C C_1 n^5 <= n^6`, so this is at
   most `C_2·(T(n^6) + n^6) = C_2·T'(n)` for a constant `C_2`. The finitely many smaller `n` are handled
   by a finite table. So `Ω` is `T'`-decidable, contradicting step 1.

So `S` is a finitely presented simple group whose word problem beats `T`. `∎`

## Where it can fail

- **The SFT premise.** `hard-quantum-rigid-free-minimal-z2-sfts-exist` is carried by the lane route
  `hard-rigid-z2-sfts-via-diagonal-hint-sequences`, which rests on
  `beta-hinted-crossing-wire-shifts-are-free-minimal-rigid`. That inherits the recalled Durand--Romashchenko
  fixed-point existence and property (p4) from `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid`.
  Its minimality part (H3) should be refereed first.
- **Khanh's import.** Finite presentation of `S` is only as good as the imported criteria of
  arXiv:2609.08428v1. Simplicity of `E_3(R)` does not use that import (item 1 of
  `central-simple-leavitt-tensor-unit-groups-are-simple`), and neither does the lower bound of step 6,
  which holds for every finitely generated group containing `Q`. The equality `S = E_3(R)` does use it,
  through item 2 of the Khanh transfer.
- **What is new.** Previously the hardest finitely presented simple groups with known word-problem
  complexity were coNP (`nV`, Birget) and coNP^⊕P (`leavitt-square-units-have-conp-parity-p-complete-word-problem`).
  This route gives no single class: for each recursive `T` a different `Ω`.
