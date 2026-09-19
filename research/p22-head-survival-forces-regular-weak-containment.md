---
rg: 2
id: p22-head-survival-forces-regular-weak-containment
kind: claim
title: The head of P_{2,2}(J) survives in some MF model iff P_{2,2}(J) is MF iff some MF model weakly contains the regular representation
distinct_from:
  binary-jacobson-head-retaining-homomorphisms-are-faithful: that is head-faithfulness for EL_5(J) through its simple finitary kernel; this proves head-faithfulness for the parabolic P_{2,2}(J), whose radical M_2(J) is abelian and not simple, through the Levi-stable ideal lattice of M_2(J), and then upgrades any head-keeping MF model to one weakly containing the regular representation.
  root-column-fixed-projection-is-not-in-root-pair-cstar: that kills a class of relative-(T) transport projections inside root-pair C*-algebras; this is a (T)-free structural reduction of the P_{2,2} lane to one MF question about the regular representation, and uses no projection or spectral gap.
  jacobson-double-parabolic-two-step-models-kill-head: that kills finite-dimensional models with a Levi-stable filtration through the leading symbol; this concerns operator-norm MF models and shows that every surviving one may be taken spectrally full on the radical and weakly containing lambda.
  leavitt-mf-survivor-yields-jacobson-regular-character: that pulls a Leavitt MF survivor back to the regular MF character of EL_5(J), a trace statement; this is a norm statement (weak containment of lambda_P) for the parabolic P_{2,2}(J), obtained from any head-keeping MF model with no trace control.
artifacts:
  - research/p22-head-survival-forces-regular-weak-containment-proof.md
  - experiments/p22-regular-weak-containment-2026-09-17/check_p22_regular.py
---

**ESTABLISHED (swarm-0917 w12, agent-verified, no referee).** No property
`(T)`, Kazhdan projection, spectral gap or trace estimate is used.

**Setting.**
* `J = F_2<S,T | TS=1>`, `Q = 1+ST`, `N = M_2(J)` (additive group).
* `P = P_{2,2}(J) = N x| L`, `L = EL_2(J) x EL_2(J)`, with
  `(A,B).Y = A Y B^{-1}`; this is the block parabolic of `EL_4(J)`.
* `h = n(E_11 Q) = x_13(Q)`, the Jacobson head.
* An **MF model** of a group `G` is a homomorphism
  `sigma: G -> U(prod_k M_{d_k} / (+)_k M_{d_k})`; `Rad_MF(G)` is the
  intersection of their kernels. `lambda_P` is the left regular
  representation; `pi` **weakly contains** `lambda_P` when
  `ker pi` is contained in `ker lambda_P` in `C*(P)`.

**Theorem.** The following are equivalent.
* (a) `h` is not in `Rad_MF(P)`.
* (b) `P` is MF, i.e. `Rad_MF(P) = 1`.
* (c) some MF model of `P` weakly contains `lambda_P`.

Moreover `Rad_MF(P)` is either `1` or contains `h`.

**Four lemmas carry it (each proved in the route).**
1. **Head-faithfulness.** Every homomorphism of `P` that does not kill `h`
   is injective. Reason: a normal subgroup meets `N` in a Levi-stable
   subgroup; Levi-stable subgroups of `M_2(J)` are exactly `M_2(I)`, `I` a
   two-sided ideal; every nonzero ideal of `J` contains `Q`; and
   `C_P(N) = N`.
2. **Topological freeness.** `L` acts topologically freely on the Cantor
   set `X = N^ = Hom(N, Z/2)`: for `l != 1` the subgroup `(l-1)N` is
   infinite, through the faithful socle `M_2((Q)) = W (x) W'`.
3. **Tensor upgrade.** If an MF model `sigma` keeps `h`, then
   `tau = (+)_{j <= J_k} sigma_k^{(x) j}` is an MF model whose spectrum on
   `N` is all of `X`, so `C*(tau(N)) = C(X)` faithfully.
4. **Archbold-Spielberg.** For a topologically free action, a
   representation of `C(X) x| L` injective on `C(X)` has kernel inside the
   kernel of the reduced crossed product `C(X) x|_r L = C*_r(P)`.

**Dichotomy.** Let `I_MF` be the intersection of the kernels in `C*(P)` of
all MF models. Either `I_MF` lies inside `ker lambda_P`, or `1-h` lies in
`I_MF`.

**Corollary for the hole (HC).** `property-t-free-jacobson-head-collapse`
holds if and only if no MF model of `EL_5(J)` restricts on `P_{2,2}(J)` to a
representation weakly containing `lambda_{P_{2,2}(J)}`. Also, the
`P_{2,2}`-local statement `h in Rad_MF(P)` holds if and only if `P` is not
MF. That local statement implies (HC).

**Class kill (where it dies).** Consider the survivors named in the w11
Attempts: MF models of `P` whose Levi unitaries mix the eigenspaces of the
radical non-pointwise.
* **Invariant:** the spectrum `Omega_sigma`, a closed subset of `X`, of the
  radical in an MF model `sigma`.
* **Step where the class dies:** the tensor upgrade. It preserves MF-ness
  and head survival, and it forces `Omega = X`.

So every `P_{2,2}`-local obstruction of the following two kinds is vacuous:
* **Spectral-support obstructions.** These say "head survives implies the
  spectrum of `N` avoids an open set", or "is contained in a proper
  Levi-invariant closed subset". This includes the eigenspace-support and
  rank-profile obstructions whose Haar case the w11 break found
  unrestricted.
* **C*-relational obstructions.** These derive, from `h != 1` in an
  arbitrary representation of `C*(P)`, a proper isometry or a nonzero index.
  They die at `lambda_P` itself. `lambda_P` keeps `h`, and `C*_r(P)` has a
  faithful trace, so it is stably finite.

A proof of the local statement must therefore show that `lambda_P` is not
weakly contained in any MF representation. That is an MF (quasidiagonal-type)
statement about the regular representation, not a finite-model statement.

**Open sufficient condition (reported, not claimed).** If `C*_r(P_{2,2}(J))`
is an MF algebra, then the `P_{2,2}`-local route to (HC) is dead: `P` would be
MF and keep `h`. Any T-free proof of (HC) would then have to use root
subgroups of `EL_5(J)` outside `P_{2,2}(J)`.

DERIVATION
p22-head-survival-forces-regular-weak-containment-proof
