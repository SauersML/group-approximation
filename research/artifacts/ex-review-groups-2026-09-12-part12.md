# EX review, groups: part 12. The fp-kazhdan-ring refill: halvable corners, rank models, finite presentation

Lane `ex-verify-groups`, 2026-09-13, ~02:15 CDT. Index: `ex-review-groups-2026-09-12.md`.
Landings by ex-fp-kazhdan-ring, 01:04–01:23.

`fp-simple-kazhdan-linear-sofic-group-exists` and `hyperlinear-fp-infinite-simple-group` compute open. The
ring route still needs a quantum rigid free minimal `Z^2`-SFT, and the finite presentation of the scalar
quotient.

## 12.1 `halvable-corner-makes-elementary-groups-nonsofic`. PASS

- **A binary Leavitt family.** `eA ≅ eA ⊕ eA` gives `s_i, t_i ∈ eAe` with `t_i s_j = δ_ij e` and
  `Σ s_i t_i = e`. So the corner ring `eAe`, with unit `e`, carries a binary Leavitt family.
- **The d-ary import.** `d-ary-leavitt-groups-nonsofic-over-finite-fields` makes `GL_n(eAe)`, `EL_n(eAe)`
  and `(eAe)^x` nonsofic.
- **Corner embedding.** `x ↦ x + (1-e) I_n` is an injective homomorphism `GL_n(eAe) -> GL_n(A)`. It sends
  `e_ij(a)` with `a ∈ eAe` to `e_ij(a)`, so `EL_n(eAe) <= EL_n(A)`.
- **Transfer to `R`.** `GL_n(M_d(R)) = GL_(nd)(R)`, and elementary matrices over `M_d(R)` are products of
  elementary matrices over `R`. Soficity passes to subgroups.
- **The separation remark.** A Sylvester rank has `rk(e) = 2 rk(e) = 0`. A faithful rank function on a simple
  ring vanishes only at `0`, so there is no halvable corner.

## 12.2 `purely-infinite-simple-algebras-have-nonsofic-el-groups`. PASS, with a note

- **The halvable corner.** By Ara–Goodearl–Pardo, the nonzero finitely generated projectives of a purely
  infinite simple ring form a group under `⊕` with cancellation. The identity `z` of that group satisfies
  `z + z = z`, and it is represented by a nonzero idempotent `e`. Cancellation turns equal classes into
  isomorphic modules, so `eR ≅ eR ⊕ eR`. This is a halvable corner, and 12.1 applies.
- **Note.** The claim states the conclusion for `R^x` and for every `n >= 2`. That needs `e` in `R` itself
  (`d = 1`), not only in some `M_d(R)`. AGP also give that every nonzero class is represented by an idempotent
  of `R`, which the import node `agp-purely-infinite-simple-rings-have-cancellative-projectives` should state
  explicitly. Otherwise the conclusion holds for ranks divisible by `d`.

## 12.3 `lef-simple-rings-are-not-finitely-presented` and `minimal-subshift-crossed-product-is-not-finitely-presented`. PASS

- The partial homomorphism on the set of subtree values of the relators extends to
  `Φ : Z<x> -> Q` agreeing on subtrees. So `Φ(w_j) = 0`, and it descends to `R -> Q` with `Φ(1) != 0`.
- By simplicity `R` embeds in the finite ring `Q`, so it is finite. The same holds for algebras over finite
  fields.
- The crossed product of an infinite minimal subshift is simple, infinite and LEF (part 1), hence not finitely
  presented.
- Credit is correctly assigned: the group form is Grigorchuk–Medynets.

## 12.4 `rank-modelled-simple-rings-give-linear-sofic-projective-el`. PASS

- **The model is faithful.** `Ψ` is injective by simplicity. Units of a rank ultraproduct are rank limits
  of invertible matrices.
- **The adjoint.** `A ⊗ A^(-T) - B ⊗ B^(-T) = (A-B) ⊗ A^(-T) + B ⊗ (A^(-T) - B^(-T))`, and
  `rk(A^-1 - B^-1) = rk(A - B)`. So `rk(Ad A - Ad B) <= 2N rk(A-B)`, a normalized 2-Lipschitz map that kills
  scalars.
- **Separation.** `rk(Ad A - 1) = N^2 - dim C(A)`, and `dim C(A) <= N max_λ dim ker(A - λ)` by the Jordan
  count. For `g ∉ Z`, faithfulness bounds `rk(Ψ(g) - λ)` below for `λ ∈ k`, and Galois symmetry gives
  `>= mN/2` off `k`.
- **Scope, correct as recorded.** Soficity is not obtained. That is Arzhantseva–Păunescu Question 8.5.

## 12.5 `free-minimal-crossed-products-are-simple-with-rank-models` and `free-minimal-subshift-elementary-groups-are-simple-kazhdan`. PASS at step level

- **Simplicity and centre.** The `d = 1` argument of part 1 §1.3–1.4 transfers verbatim with `Z^d` and
  freeness.
- **Følner rank model.** Truncating to boxes `[0,n)^d` makes the defect live on the boundary, which has
  proportion tending to `0`. Faithfulness comes from syndetic visits to a clopen set. The artifact
  `free-minimal-crossed-product-rings-and-permutive-rigidity-2026-09-13.md` was not read line by line.
- **Root detection with box towers.** The tower lemma needs bases with return times beyond `2m` in every
  direction, which freeness and compactness supply. Case (c) uses `SL_D(F_q)` with `D = 3|B_(m')| >= 27`.
  Case (d) conjugates `χ_Y u^(e_1)` just outside the tower. This mirrors part 1 §4.2, and I checked the shape
  of these steps, not the artifact text.
- Property (T) follows from finite generation. Linear soficity follows from 12.4 and the Følner model.
- Verdict PASS at step level. For `d >= 2` no soficity is claimed, which is correct.
