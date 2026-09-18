---
rg: 2
id: leavitt-refinement-identifies-unstable-k2-levels-proof
kind: route
title: Import the refinement isomorphism, compare it with stabilization by one Leavitt block conjugation, and kill the difference by padded centrality and perfectness
target: leavitt-refinement-identifies-unstable-k2-levels
requires:
  - leavitt-doubling-is-stably-conjugate-to-stabilization
  - leavitt-resolvent-stable-k2-class-is-computable
---

**Item 1** (citation). Khanh, arXiv:2609.08428, proof of Theorem `thm:steinberg-isomorphism`: "apply [Voronetsky,
§4, Proposition 1] to the ordinary groups, taking `S = {1}` ..., for the ring `M_(r+1)(R)`. Its complete family of
standard orthogonal idempotents is full and Morita equivalent, as witnessed by `E_aa = E_ab E_bb E_ba`. Merge the
last two idempotents. The maps `T_r, U_r` identify the resulting coarse presentation with `S_r`. The proposition
identifies it with the fine presentation `S_(r+1)` whenever the fine family has at least four members; here that
number is `r+1 >= 4`. Its map on generators is precisely [the formulas of item 1]. This application requires no
hypothesis on stable rank".
- Khanh states it for `L_(F_2)(1,2)`. The argument uses only the Leavitt identities, through `T_r` and `U_r`, and
  the full Morita family of matrix units, so it applies to any unital ring with a Leavitt pair.
- `φ_(r+1) D_r = α_r φ_r` is checked on generators. For example, `α_r(t_ir(a)) = t_ir(ae) t_(i,r+1)(af)`, because
  `T_r (I + a E_ir) U_r` adds `a` times the `r`-th input coordinate `ey + fz` to row `i`.
- Since `α_r` and `D_r` are isomorphisms, `D_r(K_2(r,R)) = K_2(r+1,R)`.

**Item 2.**
- **The block conjugation.** Let `V : R^(r+2) -> R^(r+2)` be the identity on the first `r - 1` coordinates. On the last
  three coordinates, where `R ⊕ R^2` is the last coordinate of `R^r` followed by the two padding coordinates, it acts
  by `V'`, which sends `(x, y, z)` to `(e*x, f*x, ey + fz)`.
- `V'` is invertible, with inverse `(p, q, w) -> (ep + fq, e*w, f*w)`, by the Leavitt identities. In block form
  `V = T_r ⊕ u` with `u(y, z) = ey + fz` and `u^-1 = (e*; f*)` (gq-referee-a, N1).
- For `A in GL_r(R)`, `V (A ⊕ 1 ⊕ 1) V^-1 = α_r(A) ⊕ 1`. The part on `R^r` is carried by `T_r`, and the padding `R^2` is
  carried isomorphically onto the last coordinate.
- **Stably.** So `stab(α_r(A)) = c_V(stab(A))` in `GL(R)`. Lifting to `St(R)`, with `GL(R)` acting on `St(R)` (Milnor),
  gives `stab ∘ D_r = c_V ∘ stab` as homomorphisms `St_r(R) -> St(R)`. Both lift the same map to `E(R)`. Their
  difference is a homomorphism from the perfect group `St_r(R)` to the central `K_2(R)`, hence trivial. This is the
  argument of `leavitt-doubling-is-stably-conjugate-to-stabilization`, item 2.
- `GL(R)` acts trivially on the centre `K_2(R)` of `St(R)` (Milnor). So `ι_(r+1) D_r = ι_r` on `K_2(r, R)`.
- `D_r` is an isomorphism `K_2(r) -> K_2(r+1)` compatible with `ι`, so it maps `U_r = ker ι_r` onto `U_(r+1)`.

**Item 3.**
- Compose the `D_r` for the isomorphisms of `U`'s and of the Steinberg groups.
- **Word problem.** `D_r` is computable on generators, and so is `D_r^-1`: given a word `y`, search for a word `x`
  and a derivation of `D_r x = y`. The search halts because `D_r` is onto, and derivations are recursively enumerable
  because `R_L` has solvable word problem (`leavitt-resolvent-stable-k2-class-is-computable-proof`).
- So solvability of the word problem, and recursive enumerability of nontriviality in `U_r`, transfer in both
  directions.

**Item 4.**
- **Two homomorphisms.** Assume `V in E_(r+2)(R)`, and let `ω_0 in St_(r+2)(R)` lift it. The maps `x -> j(D_r x)`
  and `x -> ω_0 j j(x) ω_0^-1`, from `St_r(R)` to `St_(r+2)(R)`, lift the same map to `E_(r+2)(R)`, by item 2. So their
  quotient `c(x)` lies in `K_2(r+2, R)`.
- **Padded centrality** (Khanh, Lemma `lem:padded-centrality`, proof included there, any unital ring, `m >= 3`):
  `j_m(K_2(m, R))` is central in `St_(m+1)(R)`. So after one more stabilization, `j(c(x))` is central in `St_(r+3)(R)`.
- **The difference is trivial.** `x -> j(c(x))` is then a homomorphism into a central subgroup. It is trivial
  because `St_r(R)` is perfect for `r >= 3`. With `ω = j(ω_0)`, this gives `j j D_r(x) = ω j j j(x) ω^-1`.
- **The kernel identity.** For `b >= 2`, `ker(j^(b+1) on K_2(m)) = D_m^-1(ker(j^b on K_2(m+1)))`. By induction,
  `ker(j^b on K_2(m)) ≅ ker(j^2 on K_2(m+b-2))`.
- `U_m` is the union over `b` of `ker j^b`, since `K_2(R)` is the colimit. So `U_m = 1` for all `m >= 3` if and only
  if `j^2` is injective on `K_2(m')` for every `m' >= 3`.
