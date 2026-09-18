---
rg: 2
id: mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap
kind: claim
title: Exact finite-dimensional representations of Mod(S_2) never put the whole spectrum of a separating twist near a primitive cube root of unity
distinct_from:
  mod-s2-exact-representations-have-a-torelli-scalar-gap: that asks for a uniform normalized Hilbert-Schmidt gap; this asks only for an operator-norm gap, which that claim implies because the operator norm dominates the normalized HS norm, so this is strictly weaker.
  deligne-torelli-character-counts-separating-twists: its (ST5) excludes an exact cube-root scalar; this asks for a uniform operator-norm distance from those scalars.
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that concerns all point-norm asymptotic models; this restricts to honest representations of Mod(S_2), and it is a necessary condition for that gate.
---

**OPEN.** There is `delta_0 > 0` such that every finite-dimensional unitary representation `rho` of
`M = Mod(S_2)` and every separating Dehn twist `t_s` satisfy

```text
|| rho(t_s) - omega^(+-1) I ||_op  >=  delta_0 ,        omega = exp(2 pi i/3).
```

Since `rho(t_s)` is unitary, this is a spectral statement: the spectrum of `rho(t_s)` never lies in
the open arc of radius `delta_0` around `omega` or around `omega^2`. Equivalently, `1/3` does not lie
in the closed subgroup

```text
Z_hon = { alpha : inf_rho ||rho(t_s) - exp(2 pi i alpha) I||_op = 0 }  <=  Z_op
```

of `mod-s2-real-untwisting-identifies-deligne-norm-parameters`. It is closed and a subgroup by the
same diagonal, tensor and conjugate argument as (U2).

## Position in the graph

- **Necessary for the flagship.** An honest `rho` is an asymptotic homomorphism with zero defect,
  so `Z_hon <= Z_op`. If this claim fails, then `1/3` lies in `Z_op`, so `1/3` lies in `P_op` by (U4).
  Then `Rad_MF(E_3) != C_3`, which refutes both `deligne-triple-cover-exact-mf-radical` and
  `deligne-nontrivial-maslov-opnorm-sectors-are-empty`. This is not filed as a route into this
  node, to keep the graph acyclic.
- **Sufficient with stability.** Together with `mod-s2-is-point-norm-matricially-stable`, it proves
  the gate: `deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability`.
- **Implied by the HS version.** `mod-s2-exact-representations-have-a-torelli-scalar-gap` implies
  it, since `||X||_op >= ||X||_2` for the normalized HS norm.

## Known partial information

- *Pointwise.* `delta(rho) > 0` for each single `rho`, by (ST5) and (TS4).
- *Finite image.* If `rho` factors through `M/N` with `N` of finite index, then
  `||rho(t_s) - omega^(+-1) I||_op >= sqrt(3)/l(N)`, with `l(N)` as in (E4) of
  `mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors`. This follows from (E4) because
  the operator norm dominates the normalized HS norm. It is not uniform in `N`.
- *Quantum representations.* In the SU(2) level-`k` representations the separating twist is far
  from every scalar. The tabulated normalized-HS distances squared run from `0.36` at `k = 2` up
  towards `1` at `k = 400` (`research/artifacts/hl-nh-quantum-reps-2026-09-13.md`, section 3). The
  operator norm is at least as large, so the tabulated levels stay away from the cube-root scalars.
- *Heuristic about locality.* The graph's class kill
  `deligne-flexible-subgroup-restrictions-carry-exact-sector-models` suggests the same thing here: an
  argument that only uses relations generating a Deligne-flexible subgroup will not see the
  cube-root mark. This is not transported rigorously here.

## Attempts

- **2026-09-18, swarm-0917-w9-w9-deligne-follow: algebraic scalarization and
  determinant tests both die.**
  - *Scalarization (sketch).* Suppose `rho(t_s)` is exactly scalar. Then its value is
    a separating-twist character value (TS4, ST5), which excludes the cube
    roots. Passing from near-scalar to scalar would require an algebraic
    quotient of `rho(M)` in which `t_s` becomes central.
    - Let `Q = rho(M)`, and divide by the normal closure of `[t_s, Q]`. By
      the Margulis normal subgroup theorem the result modulo the image of
      `t_s` is either finite or `Sp_4(Z)` modulo a finite group.
    - In the finite case the quotient is finite, residually finite and
      virtually cyclic, so the value of `t_s` is a tenth root of unity by
      Deligne's residual. In the other case the quotient is a central
      quotient of `M/[K,M]`, which is circular.
    - Either way the metric information `||rho(t_s) - omega|| < epsilon` is
      lost, because the quotient kills a non-small subgroup.
  - *Determinant.* `det rho` is a character of `M`, so `det rho(t_s)` is a
    tenth root of unity. If every eigenvalue is `omega e^(i eta_j)` with
    `|eta_j| < epsilon`, the product `omega^d e^(i sum eta_j)` can reach
    every tenth root once `d epsilon >= 2 pi/30`. So the test dies for
    `d >= C/epsilon`.
  - *Invariant for both.* Any test that factors through a finite quotient
    of `M` or through a one-dimensional character is bounded by the (E4)
    floor, which is not uniform in the quotient. A uniform proof needs
    information from representations with infinite image.
- **2026-09-18, swarm-0917-w10-w10-deligne-follow: a uniform Deligne-only
  floor dies at Gamma(3).** Result:
  `sp4-mess-classes-are-non-profinite-off-the-maslov-line` (ESTABLISHED).
  - *Idea.* For a Torelli-abelian finite-image model at level `Gamma'`, the
    multiplier is `(alpha/r) res b + sum_D h_D v_D`, where `v_D` are the
    pushouts of the Torelli extension along Mess orbit counts. The multiplier
    must be profinite. Hope: modulo profinite classes only the Maslov line
    survives, with Deligne's kernel `(1/2)Z`. Then `alpha/r` would be pinned
    to `(1/2)Z + O(|h|)`, uniformly in `Gamma'`, which would give (B) on this
    class.
  - *Where it dies.* On normal `Gamma'`, the conjugation symmetry of the
    orbits, together with `sum_D v_D = -(10/a) res b`, forces `m | 20/a`, where
    `m` is the number of orbits, whenever some `v_D/m` has a Maslov
    coordinate. At `Gamma(3)`, `m = 45`, so `iota(v_D/45)` is non-profinite
    and off the Maslov line. The same holds at every deeper normal level,
    with `h = 1/m -> 0`.
  - *Invariant.* The quotient `H^2(Gamma'; Q/Z) / (beta(Q) + H^2_fin)` is
    nonzero. Any proof of (B) must control all of it.
  - *By-product.* `a | 20`.
