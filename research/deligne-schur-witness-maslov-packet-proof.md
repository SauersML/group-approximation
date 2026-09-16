---
rg: 2
id: deligne-schur-witness-maslov-packet-proof
kind: route
title: Localize the Schur kernel to the coefficient packet and evaluate the Maslov class through Lie subgroup windings and rational parabolics
target: deligne-schur-witness-needs-maslov-carrying-packet
requires:
  - sp4-fd-projective-multiplier-is-finite
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
  - projective-unitary-classes-vanish-on-schur-kernel
  - nonsingular-adjunction-never-enlarges-schur-multiplier
  - schur-kernel-localizes-to-coefficient-subgroup
  - kervaire-laudenbach-holds-for-hyperlinear
  - amenable-coefficients-have-zero-schur-kernel
  - schur-kernel-shrinks-along-consequences-and-hosts
artifacts:
  - research/artifacts/sp4-schur-deligne-packet-pruning-2026-09-16.md
---

Full proofs: artifact, Sections 2--4. Exact and numerical cross-checks:
`experiments/sp4-schur-deligne-packet-pruning-2026-09-16/` (the proofs do
not depend on the numerics).

**(MP1).**

- Naturality of `ev` in the coefficients gives
  `alpha_H(y) = <e, y> mod 3`, and `<e, F> = 0`.
- A class `y in K_2` with `alpha_H(y) != 0` has a nonzero `h`-component, so
  `K_2` has rank one and `<e, K_2> = d m Z` is not in `3Z`.
- By `nonsingular-adjunction-never-enlarges-schur-multiplier`, `q_*` is onto.
  Its rational kernel contains `K_2 (x) Q != 0` inside
  `H_2(Gamma; Q) = Q`, so `H_2(A_w; Q) = 0`. Also `H_2(A_w; Z) = (Z + F)/K_2`
  is finitely generated of rank zero.
- Item 4. By (DR2) with `n = 4`, `z` survives in a finite quotient
  `Phi : Gamma_4 -> E` with `Phi(z)` of order exactly `2`. So `Phi` factors
  through `Gamma_2`. Put `c = Phi(z)`, `phi : Gamma -> E/<c>`, and
  `V = Ind_{<c>}^E sgn`. Since `c` is central it acts as `-1` on `V`, so
  `E -> U(V)` descends to `E/<c> -> PU(V)`. The multiplier of
  `Gamma -> PU(V)` evaluates as `(-1)^{<e, y>}`.
  `projective-unitary-classes-vanish-on-schur-kernel` makes it trivial on
  `K_2`.

**(MP2).**

- *Packet lemma.* Subgroups of `Gamma` are residually finite, hence
  hyperlinear. `kervaire-laudenbach-holds-for-hyperlinear` makes
  `B -> (B * <t>)/<<w>>` injective, and
  `schur-kernel-localizes-to-coefficient-subgroup` gives
  `K_2 = iota_* K_2(B, w)`.
- *Finite index.* Transfer: `[B : B_0] iota_* x = (iota o j)_* tr(x)` on
  `H_2(-; Q)`.
- *(P2), lines and 3-spaces.* Every rational line stabilizer is
  `Gamma`-conjugate to `P_K = N x| ({±1} x SL_2(Z))`, with `N` the integral
  Heisenberg group with center `C` and `C cap [N, N] = 2C`. The central
  LHS sequence gives `H_2(N; Q) = H_1(N/C; Q) (x) H_1(C; Q)` and
  `H_1(N; Q) = H_1(N/C; Q)`, and the central `m(1, -I)` acts by `-1` on
  both. A central element induces the identity on `H_p(L; V)` (Brown III.8).
  Here it also acts by `-1` on `V = H_q(N; Q)`, `q = 1, 2`, so `2` kills
  `H_p(L; V)` and it vanishes. The remaining term of total degree 2 is
  `H_2(L; Q) = 0`, since `L` is virtually free. So `H_2(P_K; Q) = 0`, and a
  rational 3-space has the stabilizer of its orthogonal line.
- *(P4).* For a connected `S` with zero winding, the lifting criterion and
  discreteness of `ker p` give a homomorphic section of `p` over `S`. So `e`
  restricts to zero on every `B_0 <= S`, and conjugation does not change the
  winding. `pi_1(SL_2(C)) = 0` gives the Bianchi case, with the Gram matrix
  of `Im det / Im omega` unimodular and symplectic basis
  `(e1, e2 - t e1, e4, e3)`. The identity component of the Siegel parabolic
  retracts onto `SO(2) <= U(2)` with `det_C = 1`, and `G` is transitive on
  real Lagrangians. This gives (P3) and the Lagrangian case of (P2).
- *(P2), symplectic planes.* The two factors `Sp(W_R)`, `Sp(W^perp_R)` have
  preimages in `G~` that commute and are universal covers with deck group
  `<z>`, because block `SL_2` has winding `±1`. So `iota^* e` is the sum
  `eps_1 + eps_2` of the factor classes. On `B_0` each projection lands in
  `SL(W cap Z^4) = SL_2(Z)`, which is virtually free, so each term pairs to
  zero.
- *(P2').* The rational hull of a `B_0`-invariant real subspace is
  `B_0`-invariant, because `B_0 <= GL_4(Q)`.
- *Non-amenability* in the checklist is
  `amenable-coefficients-have-zero-schur-kernel`. The normal-closure roots
  come from (CM1) of `schur-kernel-shrinks-along-consequences-and-hosts`.

**(MP3).** By (CM3), `K_2 <= ker phi_*`. Since `H_2(Gamma; Q) = Q`, a
nonzero `phi_* (x) Q` is injective, so `ker phi_* <= F`.

- *Block hosts.* The block inclusion `Sp_4(R) -> Sp_(2g)(R)` is an
  isomorphism on `pi_1`, so the universal cover pulls back to `G~`, and
  `<e_L, phi_* h> = d`.
- *Amalgam and HNN hosts.* This is (CM4).
