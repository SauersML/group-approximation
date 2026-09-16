---
rg: 2
id: right-child-exchange-group-is-sofic
kind: claim
title: The right-child exchange group is sofic, since the b-conjugates of its frame roots lie, window by window, in depth-monotone weighted unit groups
distinct_from:
  right-child-exchange-group-has-infinite-dihedral-root-closure: that computes the b-conjugates, finds D_inf, excludes every locally finite subgroup normalized by b, and leaves amenability, free subgroups, LEF and soficity open; this proves soficity, by showing the kernel of the quotient onto <b> is locally residually finite rather than locally finite, and leaves amenability, free subgroups and LEF open.
  depth-monotone-leavitt-subalgebras-are-stably-finite: that proves residual finiteness of finitely generated unit subgroups of one weighted part R^w_<=; this group lies in no such part (b has components of weight +a and -a), and the proof lets the weight drift with the window of b-conjugates and closes with a cyclic extension.
  sofic-subgroups-carry-independent-cylinder-defects: that turns soficity of a subgroup containing two disjoint frames into a theta = 1 model; this supplies the soficity for Gamma_b × iota_B(D_8), the one subgroup the right-child attempt entry left undecided.
  leavitt-right-child-frames-generate-infinite-order-units: that shows b has infinite order and the positive roots at A and A1 generate a finite group; this shows the whole group generated with b is sofic.
artifacts:
  - research/artifacts/right-child-exchange-group-soficity-2026-09-16.md
---

**Setting.** `R = L_(F_2)(1,2)` with code `(0, 10, 11)`, and `S[v]T[w]` is the prefix replacement `wy -> vy`. For a
cylinder `A`, `b_A = S[A0]T[A0] + S[A100]T[A10] + S[A11]T[A110] + S[A101]T[A111] + 1 - e_A`, and
`Gamma_b(A) = <iota_A(D_8), iota_(A1)(D_8), b_A>`, where `D_8 = <x_12(1), x_23(1)>`.

**Statement.**
1. **Soficity.** `Gamma_b(A)` is sofic for every cylinder `A`. So is every subgroup, in particular
   `<x, y, u, beta> ≅ <iota_A(x_23(1)), iota_(A1)(D_8), b_A>`.
2. **Structure.** At the root, let `Σ` be the four frame generators `x = 1 + S[0]T[10]`, `y = 1 + S[10]T[11]`,
   `x1 = 1 + S[10]T[110]` and `y1 = 1 + S[110]T[111]`. Put `N_b = <b^j s b^-j : j in Z, s in Σ>`.
   * `N_b` is normal and `Gamma_b / N_b` is cyclic.
   * For `n >= 1`, `Lambda_n = <b^-j s b^j : 0 <= j <= n, s in Σ>` lies in `(R^ω_≤)^x` for `ω(0) = 1`, `ω(1) = n`. So
     `N_b` is locally residually finite.
   * The weight has to drift: for `n >= 2` and `ω(1) = n - 1`, `b^-n x b^n` is outside `R^ω_≤`. And `b` lies in no `R^ω_≤` and no
     `R^ω_≥`.
3. **Conjugates.** In the frame `(0,1)`, `b = diag(1, beta)` with `beta = [[s_0, s_1t_1],[0,t_0]]`, and
   `b^-j x b^j = 1 + s_0 t_0 beta^j t_1`. Also
   * `b^-j y b^j = 1 + S[10]T[110^(2j)] + Σ_(i<j) S[110^(j-1-i)1]T[110^(j+i)1]`;
   * `b^-j x1 b^j = 1 + S[10]T[110^(2j+1)] + Σ_(i<j) S[110^(j-1-i)1]T[110^(j+1+i)1]`;
   * `b^-j y1 b^j = 1 + S[110^(j+1)]T[110^j1]`.
4. **Weight drift, general form.** Let `K` be finite and `G = <S, b> <= L_K(1,2)^x` with `S` finite and `S = S^-1`. Suppose that for
   every `n` some positive weight `ω_n` has `b^-j S b^j ⊆ R^(ω_n)_≤` for all `0 <= j <= n`, or all `⊆ R^(ω_n)_≥`. Then
   `G` is sofic.
5. **Consequence.** Let `A` and `B` be disjoint nonempty proper cylinders. Then `Gamma_b(A) × iota_B(D_8)` is sofic, so
   `sofic-subgroups-carry-independent-cylinder-defects` gives it a fixed-point-free characteristic-two rank model with
   `rk(D_A D_B) = rk(D_A) rk(D_B) = (3/8)^2`.
   * No `theta < 1` in `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` follows from the relations of
     this group together with rank calculus.
   * This closes the question the right-child attempt entry on that hole ends with. By Theorem S there, whether
     `<x, y, u, beta>` is amenable or contains free subgroups no longer matters.

**Scope.**
- The proof is artifact Sections 1–4: exact frame computations, a `Z^2`-grading bound, and the three results named in
  the route.
- It gives neither residual finiteness nor LEF of `Gamma_b`: no single weighted unit group contains `N_b`.
- Amenability of `<x, y, u, beta>` stays open. Numerics in the lane note suggest free pairs.
- A relation-only proof of the hole must still use a nonsofic subgroup containing both frames. The remaining candidates
  are `R^x` itself and `EL_3(J)`, whose soficity is the open claim `binary-jacobson-el3-is-sofic`.

## Attempts

- **Amenability of `<x, y, u, beta>` (2026-09-16): undecided, and not needed.**
  - Reduction: `beta^-1 H_0 beta ⊆ H_0` for `H_0 = <phi^j(u), phi^j(x), phi^j(y) : j >= 0>`, and the corner map
    `[[1,m],[0,d]] -> d` has abelian kernel. So amenability, and free subgroups, reduce to
    `D_0 = <d(phi^j g) : j >= 0, g in {u,x,y}>`.
  - Two pairs in `<x, y, u, beta>` match free sphere counts through radius 8 and 7, which is numerics only.
  - Leading-term certificates and vector ping-pong gave no proof.
- **Weight drift (2026-09-16): works.** Artifact Section 3. The weight `(1, n)` is sharp for the window `[0, n]`.
