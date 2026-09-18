---
rg: 2
id: deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension
kind: claim
title: Unitary sector tuples of a Deligne cover whose relator defects have rank at most k have dimension at most C(k)
artifacts:
  - research/artifacts/deligne-bounded-rank-rung-anatomy-2026-09-17.md
  - research/artifacts/deligne-bounded-rank-torsion-spectrum-2026-09-17.md
distinct_from:
  deligne-sector-truncations-have-bounded-dimension: that bounds the dimension of bounded-boundary truncations of genuine unitary sector representations; this is the rung for all rank-k sector tuples, which that node shows is equivalent to every such tuple being a truncation.
  heisenberg-irrational-center-has-rank-one-sector-tuples: that shows the analogous rung is false for the integer Heisenberg group; this is the rung for the Kazhdan non-residually-finite Deligne covers, where it is open.
  deligne-bounded-rank-monomial-models-need-large-detecting-cycles: that bounds monomial sector models over quotients Gamma/N by m A_0(N); this is the rung for arbitrary unitary tuples, with no deck group and no per-vertex holonomy.
---

**OPEN.**

**Setting.** `g >= 3`, `n >= 3`, `Gamma_n` the preimage of `Sp_(2g)(Z)` in the connected `n`-fold
cover of `Sp_(2g)(R)`, `z` the covering generator, `<S cup {z} | R>` a finite presentation with
`z^n`, `[z,s]` in `R`. Fix `zeta` with `zeta^n = 1`, `zeta^2 != 1`. A **rank-`k` sector tuple** is
`rho : S -> U(d)` together with `rho(z) = zeta I`, extended to the free group `F` on `S cup {z}`,
such that `rank(rho(r) - I) <= k` for every `r` in `R`.

**Claim.** There is `C(k)` with `d <= C(k)` for every rank-`k` sector tuple.

**Why it matters.** It is the weakest open rung of the Deligne HS ladder
(`research/artifacts/deligne-hs-metric-ladder-2026-09-13.md`). If it fails, a sequence of rank-`k`
sector tuples has normalized HS defect at most `2 sqrt(k/d)`, so `Gamma_n` has sector microstates at
rate `d^(-1/2)`.

**Equivalent forms and forced anatomy** (proofs in the artifact; each is proposed-established):

1. **Corona form (E2).** The rung fails iff for some `d_i -> infinity` there is a homomorphism
   `Gamma_n -> G_B = prod_i U(d_i) / B`, `B = {(u_i) : sup_i rank(u_i - I) < infinity}`, sending `z`
   to the class of `(zeta I)`. The class of `(zeta I)` is never trivial in `G_B`.
2. **Localization (E3).** For each `g` in `Gamma_n` with noncentral image in `Sp_(2g)(Z)` there are
   constants `N_g, A_g` (independent of `d, k`) with

   ```text
   d <= (1 + A_g) k + N_g rank(rho(g) - I)          for every rank-k sector tuple.   (LOC)
   ```

   So the rung holds iff **one** such `g` has `rank(rho(g) - I) <= r_g(k)` uniformly. The input is
   the Margulis normal subgroup theorem plus Deligne's residual `<z^2>`
   (`deligne-covers-of-sp2g-z-have-finite-residual-2z`): `z^2` lies in the normal closure of `g`.
3. **Countermodel anatomy (A1, A2).** A rank-`k` sector tuple with `d > (1 + A_g) k` has
   - **(A1) no degenerate element:** `rank(rho(g) - I) >= (d - (1 + A_g) k) / N_g` for every
     noncentral `g`;
   - **(A2) a spectral gap off `O(k)` dimensions:** with Ozawa's certificate
     `Delta^2 - eps Delta = sum xi_i^* xi_i + sum_(j <= J) a_j (r_j - 1) b_j` in `R[F]`, the
     Laplacian `rho(Delta)` has at most `k (J + 1)` eigenvalues in `[0, eps)`.

   Every countermodel is therefore an `O(k)`-dimensional perturbation of an `eps`-expander in which
   every noncentral generator moves a fixed fraction of the space. Exact representations of finite
   quotients satisfy both (A1) and (A2), so the anatomy is a firewall on constructions and does not
   prove the claim.

**Calibration.** For `H = <a,b,z | [a,b]z^(-1), [a,z], [b,z]>` the analogue is false with `k = 1`
(`heisenberg-irrational-center-has-rank-one-sector-tuples`), and (LOC) holds there with
`g = a`, `N_a = 2`, because `z = [a,b]` lies in the normal closure of `a`. So (LOC) is formal and
not a proof. Any proof must use property (T) together with the arithmetic input `<z^2>`, both of
which fail for `H`. For the residually finite extension `Sp_(2g)(Z) x Z/n`, sector representations
exist in every dimension, and (LOC) fails at exactly one step: `z^2` is not in the normal closure of `g`.

## Attempts

- **Mechanisms that provably cannot give the rung (2026-09-17, sw-021, scale-shifter).** The exact
  failing step of each is in the artifact, section D.
  - **D1, determinant and trace certificates.** `det(I + rank-k)` is unconstrained. The canonical
    trace annihilates every commutator certificate for `z`.
  - **D2, almost-invariance of joint spectra** (relative (T) pair `Z^2 x| SL_2(Z)`, Anosov
    rotation). A finite atomic measure that is invariant up to `O(k)` atoms need not be torsion:
    orbit segments of an irrational point are invariant up to 2 atoms.
  - **D3, torus certificates.** Commuting `a,b` in `Sp_(2g)(Z)` have commuting lifts in `Gamma_n`,
    because the extension class is bounded and `T^2` has simplicial volume 0. `pi_2` identities
    pair to zero as well. So a detecting certificate needs genus `>= 2` surface pieces.
  - **D4, Exel partial-representation globalization** on the good subspace `V_L`. It needs commuting
    domain projections, and general unitary tuples lack them. Globalizing positive-definite functions
    is the truncation equivalence again.
  - **D5, quantitative Deligne via bounded quasi-unipotence.** It needs `rho(x_alpha(1))^M ~ I` for a
    fixed `M`. That already fails for exact representations of `Sp_(2g)(Z/m)` as `m -> infinity`.
  - **D6, non-stable-finiteness of the twisted algebra through the corona.** `A_B` is stably finite,
    but `C_zeta[Sp_(2g)(Z)] -> A_B` need not be injective, so `YX - 1` can die.
  - **D7, transporting (LB1) to tuples.** The adjoint tuple `rho (x) rho-bar` has the exact
    invariant vector `I`, and its relator defects have rank of order `k d`, so the Kazhdan boundary
    inequality gives nothing.
- **What is left.** By (LOC) the rung is the statement that the long-root unipotent of a large
  rank-`k` sector tuple cannot move all but a bounded-rank part of `C^d` while property (T) and
  `z^2 in <<x~_alpha(1)>>` hold. The one quantitative handle not yet computed is the
  **Deligne cost** `(N_g, A_g)` of an identity `z^2 = prod_(i <= N) w_i g^(+-1) w_i^(-1) prod_(j <= A) u_j r_j^(+-1) u_j^(-1)`,
  which enters (LOC) linearly.
- **D2 repaired at atom level; the real failing step is interlacing (2026-09-17, sw-124, scale-shifter).**
  Details in `research/artifacts/deligne-bounded-rank-torsion-spectrum-2026-09-17.md`.
  - **Proposed-established.** A finitely supported integer measure on `T^2` whose defect under the two
    generators of `SL_2(Z)` is `K` equals a sum of torsion-orbit indicators plus `C_0 K` mass. The
    proof uses amenable stabilizers of non-torsion points, the Kesten gap, the Selberg (tau) gap, and
    coarea. So D2's single-generator orbit segments are not almost-invariant under `SL_2(Z)`.
  - **Dead end.** Rank-`k` tuples do not supply atom-level almost invariance. A generic rank-one
    perturbation moves all `d` eigenvalues, so rank controls only interlacing. And almost-commuting
    long-root pairs have no joint spectrum without bounded-rank `Z^2` stability (open).
  - **Barrier.** (LOC) along `x_alpha(1)^M` sees only exact `M`-torsion multiplicities, which rank
    perturbations shift by up to `M r`. With an `eps`-rank variant, Dirichlet forces `M ~ N_M^d`, and
    then the relator area must satisfy `A_M = o(log M)`. This is a heuristic barrier.
  - **Surviving target.** Monomial-type tuples, where Part I applies directly. For general tuples,
    unitary bounded-rank stability of `Z^2` is necessary but not sufficient. Even after the long-root
    pair is made to commute, the `SL_2(Z)` conjugation relations match joint spectra only up to
    interlacing, so a second, atom-level rigidity input is also needed.
- **The `Z^2` stability input is false (2026-09-17, sw-124, relaunch).** See
  `z2-commuting-pairs-are-not-bounded-rank-stable`.
  - **Counterexample.** A dislocation dipole on the `n x n` torus gives permutation matrices with
    `rank([A,B]) = 2` that are at rank distance `>= (n-4)/32 ~ sqrt(d)/32` from every commuting pair,
    over any field.
  - **Consequence.** The need posted above cannot be met. A joint-spectrum argument for the long-root
    pair must exclude dislocation-type configurations through the `SL_2(Z)` or `Sp_(2g)(Z)`
    conjugation relators.
  - **Invariant.** The obstruction is the growth of `phi(L) = rank(w_L(rho) - I)` for
    `w_L = [b^L, c^L]`, where `(b, c)` is a commuting root pair normalized by an `SL_2(Z)` in
    `Sp_(2g)(Z)`, for instance `Z^2 x| SL_2(Z)` inside `SL_3(Z)` inside `Sp_6(Z)`. Pairs near
    commuting have linear `phi`, and dislocations make it quadratic. The sharp open sub-question on
    this route is whether the `SL_2(Z)` conjugation relators of a rank-`k` tuple force
    `phi(L) <= C(k) L`.
- **The `SL_2(Z)` relators do not force linear `phi` (2026-09-17, w3-124, transplanter).** See
  `sl2-relators-do-not-force-linear-commutator-growth`.
  - **Import from Teichmueller dynamics.** Square-tiled surfaces (origamis) with Veech group
    `SL_2(Z)`. The scaled Eierlegende Wollmilchsau, with its affine group, gives permutation tuples of
    `Z^2 x| SL_2(Z)` of size `24 m^2`. Every relator has rank `<= 24`, and
    `phi(L) = rank([b^L, c^L] - I) = 12 L^2` for `L <= m`.
  - **Mechanism.** Dislocations have Burgers vectors, and `SL_2(Z)` moves them. A `4 pi` cone point
    has monodromy "go to the other sheet", which every affine map preserves.
  - **Non-split.** `Aff(O) -> SL_2(Z)` has no lift with `s^4 = 1`, because `s^4` is `-1` in `Q_8`.
    It is repaired by a diagonal `Q_8` quotient with a free 24-point `Aff(O)`-set.
  - **Dead route.** Bounded-rank control of the unipotent sector through `Z^2 x| SL_2(Z)` relators
    alone. A proof must use relators outside this subgroup, e.g. `e_31, e_32` in `SL_3(Z)`, which do
    not normalize `<e_13, e_23>`.
  - **Next falsifiable step.** Can a rank-`k` tuple of `SL_3(Z)` contain a `4 pi` cone-point
    configuration for the pair `(e_13, e_23)`? That is, is there a translation surface whose affine
    structure is compatible with both parabolics `<e_13, e_23> x| SL_2` and `<e_12, e_13> x| SL_2`?
