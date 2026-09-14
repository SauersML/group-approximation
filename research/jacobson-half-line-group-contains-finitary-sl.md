---
rg: 2
id: jacobson-half-line-group-contains-finitary-sl
kind: claim
title: The half-line five-transvection group contains every elementary transvection, so its finitary part is the simple group SL_fin(F_3) and it has index at most two in the SL_2-symbol preimage
distinct_from:
  jacobson-elementary-subgroups-are-locally-finite-by-linear: that shows every subgroup of EL_n over a finite-field Jacobson algebra is locally finite by residually finite linear; this identifies the locally finite part of one subgroup as the full finitary special linear group and pins the subgroup to index two in the symbol preimage.
  five-transvection-group-acts-on-jacobson-half-line: that constructs the half-line homomorphism and separates the eight defect elements; this shows x_23(1) lies in an infinite simple normal subgroup of the image, so no finite quotient of the image separates them.
  jacobson-image-of-five-transvection-group-is-sofic: that is the open soficity question for the image; this restates it as soficity of the symbol preimage and excludes finite and finite-dimensional witnesses.
---

**ESTABLISHED** (route `jacobson-half-line-group-contains-finitary-sl-proof`; lane `gk3-transvections`, 2026-09-14;
checked by hand, not yet independently re-derived). `experiments/gottschalk-transvections/sl_fin_ladder_check.py`
rechecks every identity of the route exactly over `F_3`: the four commutators with `X`, the window steps, the `SL_2(F_3)`
generation step, the induction conjugations for `K = 4..9` and sample commutators. All 27 checks pass
(`sl_fin_ladder_check.log`, run on MSI 2026-09-14).

**Setting.** `J = F_3<S, T | TS = 1>` acts on `F_3[N]`, and `e = 1 - ST`. Index the basis of `V = F_3[N]^2` by
`p = 2n + σ` for `e_n` in copy `σ`. As in `five-transvection-group-acts-on-jacobson-half-line`,
`Γ_V = <A, B, C, D, X> <= GL_2(J)` with `A = E_01(1)`, `B = E_10(1)`, `C = E_10(T)`, `D = E_01(S)` and
`X = diag(1, 1 + S e)`. In the single index:
- `A = I + N_A` with `N_A e_(2n+1) = e_(2n)`, and `B = I + N_B` with `N_B e_(2n) = e_(2n+1)`;
- `C = I + N_C` with `N_C e_(2n) = e_(2n-1)` for `n >= 1`, and `D = I + N_D` with `N_D e_(2n+1) = e_(2n+2)`;
- each `N` kills the other parity, and `X = I + E_31`, where `E_qp e_p = e_q`.

Let `π : GL_2(J) -> GL_2(F_3[ζ, ζ^(-1)])` be the symbol `S -> ζ`, `T -> ζ^(-1)`. Its kernel is
`GL_fin(V) = GL_2(J) ∩ (I + M_2(M_∞(F_3)))`.

**Statement.**
1. `Γ_V` contains `I + λ E_qp` for all `p != q` and `λ in F_3`. So `SL_fin(V) = ∪_M SL_M(F_3) <= Γ_V`.
2. `SL_fin(V)` is an infinite simple normal subgroup of `Γ_V` containing `X`, the image of `x_23(1)`. So every
   homomorphism from `Γ_V` into a finite group, or into the units of a finite-dimensional algebra, sends `X` to `1`
   and kills the two-root defect. `Γ_V` is not residually finite.
3. `𝒯 = π^(-1)(SL_2(F_3[ζ, ζ^(-1)]))` satisfies `Γ_V <= 𝒯` and `[𝒯 : Γ_V] <= 2`, and `𝒯` is an extension of
   `SL_2(F_3[ζ, ζ^(-1)])` by `GL_fin(V)`.

**Consequences.**
- **Dead refuters.** Through the half-line image, finite quotients and finite-dimensional models cannot refute
  `four-transvections-and-x23-force-defect-vanishing`. A nonzero-defect model has to be infinite-dimensional, like
  the sofic corner of `weakly-finite-nonzero-defect-via-sofic-jacobson-image`.
- **Intrinsic form of the soficity question.** `jacobson-image-of-five-transvection-group-is-sofic` holds exactly
  when `𝒯` is sofic, since soficity passes to subgroups and to finite-index overgroups. `𝒯` is the symbol preimage
  of `SL_2` over the Laurent polynomials in the Jacobson algebra: a finitary-linear-by-Haagerup group defined
  without reference to Leavitt units.
