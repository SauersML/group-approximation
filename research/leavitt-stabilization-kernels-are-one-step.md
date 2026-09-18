---
rg: 2
id: leavitt-stabilization-kernels-are-one-step
kind: claim
title: For a ring with a Leavitt pair, an element of St_N(R) that dies in the stable Steinberg group already dies after one stabilization, and stabilization is refinement composed with an isometric twist of the last coordinate
distinct_from:
  leavitt-refinement-identifies-unstable-k2-levels: that identifies the kernels U_N across levels, and its item 4 needs a Leavitt block in E_3 to bound the steps; this bounds them by one step with no hypothesis, by a one-line identity between refinement and stabilization.
  st-n-leavitt-resolvent-word-problem-reduces-to-k2: that reduces gate 1 to injective stability (i); this makes (i) the injectivity of a single map St_N(R_L) -> St_(N+1)(R_L).
---

**ESTABLISHED** through `leavitt-stabilization-kernels-are-one-step-proof`. Lane proof, not independently reviewed.
It is elementary given the refinement isomorphism of `leavitt-refinement-identifies-unstable-k2-levels`, item 1
(Voronetsky, read at source by gq-referee-b). No priority is claimed.

**Setting.** `R` is a unital ring with a Leavitt pair `e, f` (`e*e = f*f = 1`, `e*f = f*e = 0`, `ee* + ff* = 1`), and
`N >= 3`. `j_N : St_N(R) -> St_(N+1)(R)` is stabilization. `D_N : St_N(R) -> St_(N+1)(R)` is the refinement
isomorphism: it fixes `X_ij(a)` for `i, j < N`, and it sends `X_iN(a) -> X_iN(ae) X_(i,N+1)(af)` and
`X_Nj(a) -> X_Nj(e*a) X_(N+1,j)(f*a)`.

**Statement.**
1. **Refinement absorbs a second stabilization.** `D_(N+1) ∘ j_N = j_(N+1) ∘ j_N` as maps `St_N(R) -> St_(N+2)(R)`.
   More generally, `j_(N+k-1) ∘ ... ∘ j_N = D_(N+k-1) ∘ ... ∘ D_(N+1) ∘ j_N` for every `k >= 1`.
2. **One-step kernels.** `ker(St_N(R) -> St(R)) = ker(j_N)`. In particular, the stabilization kernel is
   `U_N = ker(K_2(N,R) -> K_2(R)) = ker(j_N)`, and it lies in `K_2(N, R)`.
3. **Stabilization is a twisted refinement.** `j_N = D_N ∘ Σ^(e)`. Here `Σ^(g)`, for an isometry `g` (`g*g = 1`), is the
   endomorphism of `St_N(R)` that fixes `X_ij(a)` for `i, j < N` and sends `X_iN(a) -> X_iN(a g*)` and
   `X_Nj(a) -> X_Nj(g a)`. The `Σ^(g)` compose as `Σ^(g) Σ^(h) = Σ^(gh)`, and `Σ^(u)` is an automorphism for a unit `u`.
   Hence `U_N = ker Σ^(e) = ker Σ^(f)`. The second equality uses `f = W e` with the unitary `W = ef* + fe*`.
4. **For `R_L`.** Condition (i) of `st-n-leavitt-resolvent-word-problem-reduces-to-k2` is equivalent to injectivity of
   the single map `j_N` at any one `N >= 3`. Equivalently, it is injectivity of the isometric twist `Σ^(s_1)` of the last
   coordinate. This supersedes item 4 of `leavitt-refinement-identifies-unstable-k2-levels`, which assumed a Leavitt
   block in `E_3` and gave two steps.

## Reading

- Membership in `U_N` is decidable (`leavitt-resolvent-stable-k2-class-is-computable`). Triviality in `U_N` is
  recursively enumerable. So gate 1 is exactly the question whether `Σ^(s_1)` can kill a nontrivial element. By item 2,
  a single application of `j_N` already reveals any such element.
- No nontrivial element of `ker Σ^(s_1)` is known. No retraction of `Σ^(s_1)` is known either: the candidate
  "untwist" `X_iN(a) -> X_iN(ae)` is not a homomorphism, since `ee* != 1`.
