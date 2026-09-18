---
rg: 2
id: virtually-fuchsian-schur-kernel-proof
kind: route
title: Separate H_2 by Q/Z classes, realize them on a visible finite-index subgroup, induce through the twisted group algebra, and apply the projective unitary vanishing theorem
target: virtually-fuchsian-coefficients-have-zero-schur-kernel
requires:
  - projective-unitary-classes-vanish-on-schur-kernel
  - schur-kernel-localizes-to-coefficient-subgroup
  - kervaire-laudenbach-holds-for-hyperlinear
artifacts:
  - research/artifacts/sp4-schur-zariski-closure-packets-2026-09-17.md
  - experiments/sp4-schur-zariski-closure-packets-2026-09-17/verify.py
---

Full proofs are in the artifact, Sections 1--2. The numerical checks in
`experiments/sp4-schur-zariski-closure-packets-2026-09-17/` (Parts C, D) are
cross-checks only.

**Standard facts recalled.**

- (F-UCT) `H^2(B; U(1)) = Hom(H_2(B; Z), U(1))`, since `U(1)` is divisible.
- (F-Hopf) For a closed orientable surface group, the class of a projective
  representation evaluates on `[M]` as the scalar image of the product of
  commutators of the lifted generators.
- (F-top) Noncompact surfaces have `H_2 = 0` (Hatcher, Prop. 3.29).
- (F-Sel) Selberg's lemma.

**Lemma IND.** Let `S <= B` have index `m`, and let `c` be a normalized
`U(1)`-cocycle on `B` with `[c|_S]` the multiplier of `phi : S -> PU(n)`.
Then `[c]` is the multiplier of some `rho : B -> PU(nm)`.

1. Lift `phi` to `pi` with `pi(s) pi(s') = c(s, s') pi(ss')` exactly.
2. Form `V = C^c[B] (x)_{C^c[S]} C^n`. `C^c[B]` is free over `C^c[S]` on a
   transversal `u_{r_i}`, so `dim V = nm`.
3. Put `rho(g) = u_g .`, so that `rho(g) rho(h) = c(g, h) rho(gh)`.
4. If `g r_j = r_i s`, then `rho(g)` maps block `j` to block `i` by
   `c(g, r_j) conj(c(r_i, s)) pi(s)`, which is unitary.

**Lemma VIS.**

- *Finite `S`.* Twisted regular representations
  (`projective-unitary-classes-vanish-on-schur-kernel`, as stated there).
- *Torsion-free Fuchsian `S`.* `H^2/S` is a `K(S, 1)` surface.
  - Noncompact: (F-top).
  - Closed of genus `g >= 2`: `[X_q^k, Y_q] = zeta_q^k I` gives a projective
    representation, and by (F-Hopf) its class is `k/q` on `[M]`.

**Theorem.**

1. Let `0 != x in H_2(B)`. Since `Q/Z` is an injective cogenerator, there is
   `f : H_2(B) -> Q/Z` with `f(x) != 0`. By (F-UCT) it is a `U(1)`-cocycle
   class `[c]`.
2. `f o iota_*` on `S` is `Q/Z`-valued, so by visibility it is the multiplier
   of some `phi : S -> PU(n)`.
3. By IND, `[c]` is the multiplier of some `rho : B -> PU(n [B : S])`.
4. Apply `projective-unitary-classes-vanish-on-schur-kernel` to the countable
   group `B`, taking `d_k = n[B : S]` for all `k` and `N` the kernel of the
   first-coordinate projection. Then `U = U(n[B : S])`, `A = U(1)` and
   `T = PU(n[B : S])`. So `beta_rho` vanishes on `K_2(B, w)`, and
   `x` is not in `K_2(B, w)`.
5. Hence `K_2(B, w) = 0`.
6. `kervaire-laudenbach-holds-for-hyperlinear` makes
   `B -> (B * <t>)/<<w>>` injective. Then
   `schur-kernel-localizes-to-coefficient-subgroup` gives
   `K_2(Q, w) = iota_* K_2(B, w) = 0`.

For finitely generated virtually Fuchsian `B`, take `S` torsion-free by
(F-Sel). Residual finiteness gives hyperlinearity.
