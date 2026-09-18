---
rg: 2
id: leavitt-refinement-identifies-unstable-k2-levels
kind: claim
title: For a ring with a Leavitt pair, Voronetsky refinement gives isomorphisms St_r(R) ≅ St_(r+1)(R) for r >= 3 compatible with stable K_2, so the stabilization kernels U_r of R_L are all isomorphic and injective stability, and the word problem, hold at one level iff at every level
distinct_from:
  leavitt-doubling-is-stably-conjugate-to-stabilization: that proves the doubling St_N(R) ≅ St_N(M_2(R)) -> St_2N(R) is stably conjugate to stabilization and leaves open whether the block map is bijective on K_2; this imports the refinement isomorphism St_r ≅ St_(r+1), which settles the one-step form of that bijectivity.
  leavitt-resolvent-stable-k2-class-is-computable: that proves condition (ii) and reduces gate 1 to the kernels U_N; this shows those kernels do not depend on N >= 3.
---

**ESTABLISHED by citation plus a short argument**, through `leavitt-refinement-identifies-unstable-k2-levels-proof`.
Refereed: gq-referee-a PASS on items 2--4, proof-gap lens (report 2d373a8ea, N1 and N2 applied); gq-referee-b PASS on item 1,
citation lens (report dcf202f7c, W1 applied).
- Item 1 is Voronetsky, arXiv:2004.08551v2, read at source by gq-referee-b. §2, p. 3 covers any unital ring with a
  complete family of Morita-equivalent orthogonal idempotents. The map `F_α` on p. 5 has exactly the formulas of
  item 1. On p. 9, before Lemma 5: for `S = {1}`, `F_α : St(R, Φ/α) -> St(R, Φ)` "is a surjection for n >= 3 and a
  bijection for n >= 4", and `St(R, Φ)` is perfect for `n >= 3`. Proposition 1 (p. 10) has no stable-rank,
  commutativity or finiteness hypothesis. It is applied to `M_(r+1)(R)`, where `α_r` carries the standard family of
  `M_r(R)` to `(E_11, ..., E_(r-1,r-1), E_rr + E_(r+1,r+1))`, as in Khanh, arXiv:2609.08428, proof of Theorem
  `thm:steinberg-isomorphism`.
- No priority is claimed.

**Setting.** `R` is a unital ring with a Leavitt pair `e, f, e*, f*`: `e*e = f*f = 1`, `e*f = f*e = 0`,
`ee* + ff* = 1`. For `R_L` take `e = s_1`, `f = s_2`, `e* = t_1`, `f* = t_2`. Let `r >= 3`.
- `T_r : R^r -> R^(r+1)` fixes the first `r - 1` coordinates and sends the last coordinate `x` to `(e*x, f*x)^T`.
- `U_r : R^(r+1) -> R^r` fixes the first `r - 1` coordinates and sends the last pair `(y, z)` to `ey + fz`.
- `U_r T_r = I_r`, `T_r U_r = I_(r+1)`, and `α_r(A) = T_r A U_r` is a unital ring isomorphism `M_r(R) -> M_(r+1)(R)`.

**Statement.**
1. **Refinement isomorphism** (Voronetsky, via Khanh). The assignments
   - `D_r X_ij(a) = X_ij(a)` for `i, j < r`,
   - `D_r X_ir(a) = X_ir(ae) X_(i,r+1)(af)` for `i < r`,
   - `D_r X_rj(a) = X_rj(e*a) X_(r+1,j)(f*a)` for `j < r`,
   define an isomorphism `D_r : St_r(R) -> St_(r+1)(R)` with `φ_(r+1) D_r = α_r φ_r`. So `D_r` maps
   `K_2(r, R)` onto `K_2(r+1, R)`.
2. **Compatibility with stable `K_2`.** `ι_(r+1) ∘ D_r = ι_r` on `K_2(r, R)`, where `ι` denotes stabilization to `K_2(R)`.
   So `D_r` restricts to an isomorphism `U_r -> U_(r+1)` of stabilization kernels.
3. **Level independence for `R_L`.**
   - All `U_r`, `r >= 3`, are isomorphic.
   - Injective stability (i) holds at one level `r >= 3` if and only if it holds at every level.
   - `St_r(R_L) ≅ St_3(R_L)` for all `r >= 3`. So the word problem of `St_r(R_L)` is solvable at one level iff at
     every level, and the same holds for recursive enumerability of nontriviality in `U_r`.
   - Gate 1 is the same question at `N = 3, 4, 5` or `10`.
4. **Bounded-step form** (superseded by `leavitt-stabilization-kernels-are-one-step`, which gives one step with no
   hypothesis). Suppose that `V' = [[e*, 0, 0], [f*, 0, 0], [0, e, f]]` lies in `E_3(R)`. Then
   `V_m = I_(m-1) ⊕ V'` lies in `E_(m+2)(R)` for every `m >= 3`, which the kernel identity at all levels needs
   (gq-referee-a, N2). Then for `x in St_r(R)`,
   `j j (D_r x) = ω · j j j (x) · ω^-1` in `St_(r+3)(R)` for some `ω`, where `j` is one-step stabilization. It follows
   that `U_3 = 1` if and only if `j ∘ j` is injective on `K_2(m, R)` for every `m >= 3`. Whether `V' in E_3(R_L)` is not
   decided here. It holds if `GL_3(L_Q(1,2)) = E_3(L_Q(1,2))`.

## What remains for (i)

- An **absolute input at one level** is still needed. Khanh's comparison criterion (Theorem `thm:raw-criterion`)
  gives `K_2(4, R) = 1` for `L_(F_2)(1,2)`. It uses `GL = E` in ranks `n - 1, n - 2`, the vanishing
  `j(K_2(n-1)) = 1`, and a simply connected frame complex. The first two fail for `R_L`, since `K_1(R_L) = Z` and
  `K_2(R_L) = Q^x`.
- A **relative version** would be the natural next step: frame-complex connectivity for `R_L` giving injectivity of
  `K_2(n-1) -> K_2(n)` rather than vanishing. It needs an analogue of Khanh's simultaneous word-multiplier lemma
  (`lem:word-multiplier`) for `R_L`: one right multiplier `x` with `η_i^* a_i x = 1` for finitely many nonzero `a_i`.
  Khanh proves this for `L_(F_2)(1,2)` by word combinatorics over `F_2`. It is not proved here for `R_L`.
- No explicit nontrivial element of any `U_r` is known.
