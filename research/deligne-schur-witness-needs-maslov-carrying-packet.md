---
rg: 2
id: deligne-schur-witness-needs-maslov-carrying-packet
kind: claim
title: A Deligne Schur witness over Sp4(Z) has an even rank-one killed image and a Maslov-carrying, strongly irreducible coefficient packet
distinct_from:
  sp4-schur-kernel-meets-the-deligne-triple-class: that is the open existence of a witness; this lists necessary conditions that every witness must satisfy and prunes whole families of coefficient packets.
  real-symplectic-solutions-kill-no-deligne-schur-class: that prunes by solvability of the equation in some Sp_2g(R); this prunes by where the coefficients sit, through the second homology of any subgroup containing them, whatever the equation and whether or not it has a real solution.
  amenable-coefficients-have-zero-schur-kernel: that removes coefficient subgroups with Connes-embeddable twisted algebras, such as amenable ones; this removes non-amenable packets (parabolics, real Lagrangian and rational symplectic plane stabilizers, Bianchi groups) by the Maslov class alone.
  amenable-t-shape-adjunctions-kill-no-schur-class: that prunes by the t-shape over torsion-free coefficient subgroups; this prunes by the position of the coefficients inside Sp_4(R), at every shape and with torsion allowed.
  schur-kernel-shrinks-along-consequences-and-hosts: that is the elementary comparison of Schur kernels for any group; this specializes it and adds the Maslov class, Deligne's residual computation and packet geometry specific to Sp_4(Z).
artifacts:
  - research/artifacts/sp4-schur-deligne-packet-pruning-2026-09-16.md
---

**Setting.** `Gamma = Sp_4(Z)`, `G = Sp_4(R)`, `p : G~ -> G` the universal
cover with deck group `<z> = Z`, `Gamma~ = p^{-1}(Gamma)` with class
`e in H^2(Gamma; Z)`, and `Gamma_n = Gamma~/<z^n>` with class `e_n = e mod n`.
Deligne's multiplier is `alpha = e_3`. Write
`H_2(Gamma; Z) = Z<h> + F` with `F` finite and `<e, h> = d != 0`
(`sp4-fd-projective-multiplier-is-finite`, proof route, Steps 0 and 3).
A **witness** is a nonsingular `w in Gamma * <t>` with
`alpha_H(K_2(Gamma, w)) != 0`. Write `K_2 = K_2(Gamma, w)` and
`A_w = (Gamma * <t>)/<<w>>`.

**(MP1) Shape of the killed image.** For every witness:

1. `3` does not divide `d`;
2. `K_2` has rank one, and `<e, K_2> = d m Z` with `m >= 1` and `3` not
   dividing `m`;
3. `H_2(A_w; Q) = 0`, and `H_2(A_w; Z)` is finite;
4. `<e, K_2> <= 2Z`, so `d m = ±2 mod 6`.

Item 4 uses the inclusion `Res_fin(Gamma_4) <= <z^2>` of display (DR2) in
`deligne-covers-of-sp2g-z-have-finite-residual-2z`. Earlier graph uses
consumed only the reverse inclusion.

**(MP2) Packet pruning.** Call `B <= Gamma` *Maslov-carrying* if
`<e, iota_* H_2(B; Z)> != 0`, equivalently if
`iota_* : H_2(B; Q) -> H_2(Gamma; Q)` is nonzero. If `B` contains the
coefficients of `w`, then `K_2 <= iota_* H_2(B; Z)`. Suppose some
finite-index `B_0 <= B` satisfies one of:

- (P1) `H_2(B_0; Q) = 0`;
- (P2) `B_0` preserves a proper nonzero rational subspace of `Q^4`. This
  covers lines and 3-spaces, where the stabilizers are conjugate to the
  Klingen parabolic and `H_2(P_K; Q) = 0`. It covers Lagrangian planes, and
  symplectic planes with any lattice discriminant;
- (P2') `B_0` preserves a real subspace whose rational hull is proper;
- (P3) `B_0` preserves a real Lagrangian subspace, rational or not;
- (P4) `B_0` lies in a `G`-conjugate of a connected Lie subgroup `S <= G`
  with `pi_1(S) -> pi_1(G)` zero. Examples: `SL_2(C)` preserving `Im det`,
  hence all Bianchi groups `SL_2(O_d)` embedded through the integral form
  `Im det / Im omega`; the diagonal `SL_2(R)` in `omega + (-omega)`; the
  identity component of the Siegel parabolic.

Then `B` is not Maslov-carrying, and `w` is **pruned**: `<e, K_2> = 0`, so
`K_2 <= F` and every `ev(e_n)`, `n >= 1`, vanishes on `K_2`. In particular
`w` is not a witness.

**(MP3) Rational hosts.** Let `phi : Gamma -> L` satisfy
`phi_* (x) Q != 0` on `H_2(-; Q)`, and suppose `w_phi` has a solution in `L`.
Then `K_2 <= F`. This holds for groups `L <= Sp_(2g)(R)`, `g >= 2`,
containing the block image of `Gamma`. It also holds for iterated amalgams
and HNN extensions of `Gamma` along subgroups with vanishing rational
second homology, such as root adjunctions, and for directed unions and
composites of these constructions.

**Consequence (witness checklist).** Let `w` be a witness and let `B` be
any subgroup containing its coefficients. Then `B` is non-amenable and
Maslov-carrying. No finite-index subgroup of `B` preserves a proper rational
subspace, a real Lagrangian, or a real subspace with proper rational hull.
No finite-index subgroup lies in a conjugate of a winding-zero connected Lie
subgroup. Every nonsingular normal-closure root of `w` is again a witness.
The direct search must therefore use strongly `Q`-irreducible packets with
nonzero rational image in `H_2(Gamma; Q)`: finite-index subgroups, or thin
packets not inside any winding-zero subgroup.

**Scope.** This does not prove or refute the target. Relative to
`real-symplectic-solutions-kill-no-deligne-schur-class`, (MP3) is modest:
with the universal cover as host extension, (RS1) already gives the same
conclusion for `Sp_(2g)(R)` hosts and for root adjunctions. The Hilbert
modular packets, the real Klingen parabolic and the principal `SL_2` have
nonzero winding and are not pruned here.

DERIVATION
deligne-schur-witness-maslov-packet-proof
