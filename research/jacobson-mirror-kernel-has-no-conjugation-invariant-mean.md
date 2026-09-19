---
rg: 2
id: jacobson-mirror-kernel-has-no-conjugation-invariant-mean
kind: claim
title: Property (T) of the mirror half kills every kernel-averaging descent from P to EL_n(J), because no mean on P is invariant under conjugation and under left translation by the mirror kernel
distinct_from:
  coherent-kernel-folner-windows-force-conjugation-invariant-mean: that proves coherent Følner windows along a normal kernel produce the mean (CIM) and identifies (CIM) with co-amenability of the diagonal in the fibre square; this proves (CIM) fails for the Jacobson mirror quotient (P, 1 x L_-) and for (EL_n(J), L), and more strongly that no mean on the whole ambient group is invariant under conjugation and one kernel translation.
  bilateral-envelope-fuses-the-mirror-kernel-with-the-head: that kills approximations inherited from groups in which the mirror head is conjugate to the head (H_bi, P plus a swap, periodic models) through a conjugacy in the envelope; this kills compressions of the regular representation of P itself, and of every group mapping onto the mirror half, by spectral gap. The envelope conjugacy is never used.
  jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group: that reduces soficity of EL_n(J) to the quotient step P -> P / L_- and records in (MQ5) that no finite kernel is normalized; this shows the averaging mechanism that proves finite-kernel permanence has no infinite analogue here, by property (T) of E_-.
  sofic-quotients-by-finite-normal-subgroups-are-sofic: that passes soficity to quotients by finite kernels; this names the obstruction to the tracial analogue of that argument, the central projection |N|^-1 sum_(n in N) u_n, for the infinite kernel L_-.
  kazhdan-groups-mean-free-amenable-iff-residually-finite: that shows invariant means of Kazhdan actions live on finite orbits; this applies it to the conjugation action of the mirror half and adds the kernel translation that the finite-orbit part cannot absorb.
  kun-thom-wreath-actor-subgroups-are-not-co-amenable: that uses a Kazhdan-forbidden mean on the affine lamp space of a wreath product; this is the same spectral-gap mechanism applied to a non-split extension with a Kazhdan quotient, the Jacobson mirror fibre product.
artifacts:
  - research/artifacts/jacobson-mirror-kernel-no-conjugation-mean-2026-09-18.md
---

**ESTABLISHED** (route `jacobson-mirror-kernel-no-conjugation-mean-proof`). Unreviewed.

**Notation.**
- As in `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`: `n >= 3`, `E_+ = EL_n(J)` on `V_+^n`,
  `E_- = EL_n(J)` on the mirror half `V_-^n`, and `P = E_+ x_(SL_n(A)) E_-`. `EL_n(J) = P / (1 x L_-)`.
- For a group `W`, `FC(W)` is the set of elements with finite conjugacy class. It is a characteristic subgroup.
- A *mean* on a set `X` is a finitely additive probability measure on all subsets of `X`.
- `L(G)` is the group von Neumann algebra with trace `tau`, and `||x||_2 = tau(x^* x)^(1/2)`.

**Theorem A (spectral-gap kill of kernel means).** Let `G` be a countable group, `W` a group with property (T),
`phi : G -> W` a surjective homomorphism, and `k_0 in G` with `phi(k_0) notin FC(W)`. Then no mean `m` on `G`
satisfies both
- `m(g A g^-1) = m(A)` for all `g in G` and `A ⊆ G`, and
- `m(k_0 A) = m(A)` for all `A ⊆ G`.

**Theorem B (no rescaled regular compression).** In the setting of Theorem A there are a finite `F ⊆ G` and
`epsilon > 0`, depending only on `(G, phi, k_0)`, with the following property. Let `(B, tau_B)` be any tracial
von Neumann algebra and `v : G -> U(B)` any homomorphism. Put `M = L(G) ⊗̄ B` and `U_g = lambda_g ⊗ v_g`. Then no
nonzero `x in L^2(M)` satisfies

```text
||U_g x U_g^* - x||_2 <= epsilon ||x||_2   for all g in F,      ||U_(k_0) x - x||_2 <= epsilon ||x||_2.
```

In particular no nonzero projection `p in M` does.

**Theorem C (the Jacobson instance).** Take `G = P`, `W = E_-`, `phi = pr_- : (g,h) |-> h`, and
`k_0 = (1, t)` with `t in L_-` any nonidentity element, for example a finitary transvection. The hypotheses hold:
`E_- = EL_n(J)` has property (T) (`elementary-groups-over-fg-rings-have-property-t`), `pr_-` is onto, and `t` has
infinite conjugacy class in `E_-`. Hence:
1. **(CIM) fails for `(P, 1 x L_-)`.** No mean on `L_-` is invariant under left translation by `L_-` and under
   conjugation by `P`. Equivalently, the diagonal is not co-amenable in `P x_(EL_n(J)) P`.
2. **Same for the Toeplitz group itself.** (CIM) fails for `(EL_n(J), L)`, taking `G = W = EL_n(J)`.
3. **No coherent Følner windows.** No sequence of coherent windows in `L_-` along `P`, or in `L` along
   `EL_n(J)`, is asymptotically Følner (item 1 of `coherent-kernel-folner-windows-force-conjugation-invariant-mean`).
   This covers equivariant Ornstein–Weiss quasi-tilings of `L_-`-orbits in any auxiliary `P`-system.
4. **No compression of the regular representation.** Theorem B applies with `k_0 = (1,t)`. Let `p_i` be
   nonzero projections in `L(P) ⊗̄ B_i`, with `U = lambda ⊗ v_i` as in Theorem B and the trace on `p_i M_i p_i`
   renormalized by `tau(p_i)` (so `tau(p_i) -> 0` is allowed). Then the compressions `g |-> p_i U_g p_i` cannot be
   approximately multiplicative on every finite set and also send `(1,t)` to within `o(1)` of `p_i` in the
   renormalized 2-norm. So `L(EL_n(J))`, and every tracial image of `EL_n(J)` that is nontrivial on `L`, cannot be
   carved out of the regular representation of `P`, or out of any `lambda_P ⊗ v`, by rescaled almost-invariant
   projections. (One nontrivial `t` suffices, so this holds even when only one kernel element is required to die.)

**What this kills.** The class of *kernel-averaging descents* for the open quotient step of
`binary-jacobson-el3-is-sofic`, and for its hyperlinear version, the load-bearing reduction of
`agent-leavitt-not-bcs-negative-root-corner`.
- **Invariant.** Property (T) of the mirror half `E_-`, together with `L_- ∩ FC(E_-) = 1`.
- **Step where the class dies.** "Average the kernel": the averaging measure or projection must be almost
  invariant under conjugation by the generators of `P`. The Kazhdan gap then pushes it onto `FC(E_-) = 1`, where
  left translation by `t` moves it off itself.
- **The finite-kernel mechanism.** For finite `N ◁ G` the projection `p_N = |N|^-1 sum_(n in N) lambda_n` is
  central and fixed by `N`, and `p_N L(G) = L(G/N)`. That is the tracial form of
  `sofic-quotients-by-finite-normal-subgroups-are-sofic`. Theorem B is the precise statement that no approximate
  version of `p_N` exists for `L_-` inside `P`.

**What it does not say.** Theorem A kills a method, not the conclusion.
- *Calibration.* `G = Z^3 x| SL_3(Z)` is Kazhdan (`affine-semidirect-sl3-source-has-property-t`), and `k_0 = e_1`
  has infinite orbit. So (CIM) fails for `(G, Z^3)`, although `G / Z^3 = SL_3(Z)` is residually finite.
- **Survivors.**
  - Approximations of `P` whose kernel-averaging projection sits in the relative commutant of a *non-regular*
    tracial representation (for instance inside `R^omega`), where the conjugation representation of `P` on `L^2` is
    not of the form "conjugation on `l^2(P)` tensor anything".
  - Approximations of `EL_n(J)` built directly, without passing through `P`.
  - Of these, the ones inherited from `H_bi`, from `<P, c>`, or from the periodic models are already dead
    (`bilateral-envelope-fuses-the-mirror-kernel-with-the-head`).
- **Consequence for Kourovka 21.118.** Any general theorem "residually finite, or LEF, modulo amenable is sofic
  (or hyperlinear)" that is strong enough to settle `EL_n(J)` cannot be proved by kernel averaging. It must work
  for pairs `(G, N)` in which `N` injects, with infinite classes, into a Kazhdan quotient of `G`.
