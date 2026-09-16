# Swarm notes: sp4-schur-kernel-meets-the-deligne-triple-class (2026-09-16)

Target (OPEN): some nonsingular `w in Sp_4(Z) * <t>` kills a Schur class
detected by Deligne's mod-3 multiplier `alpha = e_3`.

Outcome: **obstruction / necessary conditions**. No witness was found, and
the target is not refuted.

## Files

- Artifact (full proofs):
  `research/artifacts/sp4-schur-deligne-packet-pruning-2026-09-16.md`
- Claim `research/schur-kernel-shrinks-along-consequences-and-hosts.md`
  (general lemmas for any group), with route
  `research/schur-kernel-consequence-host-proof.md`.
- Claim `research/deligne-schur-witness-needs-maslov-carrying-packet.md`
  (witness shape, packet pruning, rational hosts), with route
  `research/deligne-schur-witness-maslov-packet-proof.md`.
- Experiments: `experiments/sp4-schur-deligne-packet-pruning-2026-09-16/`
  (`verify.py`, `output.txt`, ends `ALL PASS`).

## Setup

- `Gamma = Sp_4(Z)`, `G = Sp_4(R)`, `p : G~ -> G` universal cover,
  `Gamma~ = p^{-1}(Gamma)` with class `e`, and `Gamma_n = Gamma~/<z^n>` with
  class `e_n`.
- `H_2(Gamma; Z) = Z<h> + F` with `F` finite and `<e, h> = d != 0`, from
  `sp4-fd-projective-multiplier-is-finite`, proof route Steps 0 and 3.
- `K_2(Q, w) = ker(H_2(Q) -> H_2((Q * <t>)/<<w>>))`.

## What was proven (artifact Sections 1--4)

1. **Consequence monotonicity (any group).** If `w in <<u>>`, then
   `K_2(w) <= K_2(u)`. So pruning by asphericity or by amenable torsion-free
   shape spreads to every nonsingular consequence, including proper powers
   and products of conjugates.
2. **Host bound.** A solution in a host `L` gives `K_2 <= ker phi_*`.
   Amalgams and HNN extensions along rationally 2-acyclic subgroups are
   rationally injective on `H_2`.
3. **Witness shape.**
   - `3` does not divide `d`.
   - `K_2` has rank one, and `<e, K_2> = d m Z` with `3` not dividing `m`.
   - `H_2(A_w; Q) = 0`.
   - `<e, K_2> <= 2Z`. This uses a finite quotient of `Gamma_4` with `z` of
     order 2, an induced representation, and
     `projective-unitary-classes-vanish-on-schur-kernel`. It consumes the
     inclusion `Res_fin(Gamma_4) <= <z^2>` of (DR2).
4. **Packet pruning.** Call `B` Maslov-carrying if
   `<e, iota_* H_2(B)> != 0`. By KL for hyperlinear groups and localization,
   a witness needs every coefficient-containing `B` to be Maslov-carrying.
   Not Maslov-carrying, hence pruned:
   - (P1) packets with `H_2(-; Q) = 0`;
   - (P2) packets preserving any proper rational subspace:
     - lines and 3-spaces, via Klingen `H_2(P_K; Q) = 0` (Heisenberg LHS
       plus the central `-1` trick);
     - Lagrangian planes;
     - symplectic planes with any discriminant, via the product-extension
       identity `iota^* e = eps_1 + eps_2` and `SL_2(Z)` virtually free;
   - (P2') packets preserving a real subspace with proper rational hull;
   - (P3) packets preserving a real Lagrangian;
   - (P4) packets inside winding-zero connected Lie subgroups: Siegel `P_S^0`,
     `SL_2(C)` and hence all Bianchi groups (explicit unimodular integral form
     `Im det / Im omega`), the diagonal `SL_2` in `omega + (-omega)`, and
     `D^1(R)` with `nrd mu < 0`.
5. **Rational hosts.** If `phi_* (x) Q != 0` and `w_phi` is solvable, then
   `K_2 <= F`. Honest comparison: with the universal cover as the host
   extension, (RS1) of `real-symplectic-solutions-kill-no-deligne-schur-class`
   already gives this for `Sp_(2g)(R)` hosts and for root adjunctions. The
   new content here is modest.

## Approaches tried and where each dies

- **Bounded cohomology / Maslov quasimorphism counting on van Kampen
  diagrams.** `e` is bounded on `Gamma`, and a killed class is a relative
  2-cycle in `A_w`. This dies because `e` has no extension to `A_w`, and the
  `t`-cells contribute uncontrolled amounts. There is no a priori bound on
  the number of `t`-cells.
- **Homeomorphism hosts.**
  - `Homeo` of the universal cover of the Lagrangian Grassmannian: `G~` acts,
    so `Gamma~` extends. But solvability of `w` there is not controlled, so
    nothing is proved. Unverified.
  - `Homeo^+(S^1)` hosts with the Euler class: higher-rank lattices acting on
    the circle have finite orbits (Ghys; Burger--Monod; recalled, not
    re-fetched, unverified). So there is no rational detection of `h`.
- **Zariski density of a witness packet.** It is not forced. The principal
  `SL_2` (winding `-2`), Hilbert modular packets (windings `(1,1)`) and
  `omega + omega` (winding 2) survive every criterion here.
- **Degree theory for word maps `T -> w(T)` on `Sp_4(R)`.** The map is not
  proper, so there is no degree argument forcing real solutions. Dies
  immediately.
- **p-adic hosts.** A continuous central extension of `Sp_4(Z_p)`, `p` odd,
  is expected to split. This is the standard picture, recalled but not
  re-read, so it is unverified. So only mod-2 information appears, and
  `alpha` is mod 3.
- **Metric ultraproduct hosts.** Only projective-unitary multipliers are
  controlled
  (`projective-unitary-classes-vanish-on-schur-kernel`), and Deligne's class
  is invisible to finite-dimensional unitary data. This dies by design.
- **Root-type equations `t^m = g`.** The adjunction is a root adjunction, so
  Mayer--Vietoris gives zero rational kernel. These are pruned (Section 1).
- **Relative amenability / soficity (Ji--Ogle--Ramsey).** The paper is
  withdrawn, so it was not used.

## Where a witness search must go

- Coefficients generating a finite-index subgroup of `Gamma`, or thin packets
  that are strongly `Q`-irreducible, not inside any winding-zero subgroup, and
  with nonzero rational image in `H_2(Gamma; Q)`.
- `w` with no solution in any `Sp_(2g)(R)` and none in root adjunction hosts.
- `H_2(A_w; Q) = 0` and `<e, K_2>` even.
- Every normal-closure root of `w` again a witness. In particular no root is
  aspherical or of amenable torsion-free shape.

## Open edges

- Real lines or real symplectic planes with rational hull `Q^4` (real Klingen
  parabolic and real splittings have winding 1).
- Hilbert modular packets are expected to be Maslov-carrying, but this is
  not proved.
- Classification of winding-zero subgroups was not attempted.
- An independent check of the (DR2) inclusion `Res_fin(Gamma_4) <= <z^2>`
  (residual finiteness of the metaplectic double cover) is needed for item 3.

## Parallel work noticed

An in-flight, not landed, node by another agent,
`deligne-multiplier-trivial-on-sl2xsl2-and-parabolics`, shows that `alpha` is
a circle coboundary on `SL_2(Z) x SL_2(Z)`, `P_S(Z)` and `P_K(Z)`. It
overlaps the standard cases of (P2) mod 3. The artifact (Remark 3.7'') says
what is different here: an integral pairing, irrational Lagrangians,
non-unimodular planes, and winding-zero packets.

## Literature (consulted 2026-09-16 via arXiv abstract pages unless marked)

- M. Stover, arXiv:2407.07680 (Thm 1.5, Deligne; quoted in graph, not
  re-read).
- R. Ji, C. Ogle, B. Ramsey, arXiv:1807.07600 (withdrawn v4, 2019-01-10).
- L. Funar, W. Pitsch, arXiv:2004.04129 (background).
- A. A. Klyachko, M. A. Mikheenko, V. A. Roman'kov, arXiv:2303.13240
  (background).
- M. A. Mikheenko, arXiv:2309.09096 and arXiv:2410.20729 (background).
- M. Nitsche, A. Thom, arXiv:1811.07737 (pinned in graph).
- A. A. Klyachko, arXiv:math/0409146 (background).
- Unverified, recalled only:
  - Ghys and Burger--Monod on circle actions of higher-rank lattices;
  - Borel density;
  - `H_1(Sp_4(Z)) = Z/2`;
  - Brown, *Cohomology of Groups*, GTM 87.

None of these studies Schur kernels of adjunctions over `Sp_4(Z)`.
