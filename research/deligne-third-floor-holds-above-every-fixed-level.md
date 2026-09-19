---
rg: 2
id: deligne-third-floor-holds-above-every-fixed-level
kind: claim
title: Classes pulled back from a fixed finite-index subgroup of Sp_4(Z) keep a third cellular floor on every Schreier complex above it, because the profinite multiplier is finite
distinct_from:
  deligne-schreier-complexes-have-a-uniform-third-cellular-floor: that is the floor for all classes on all Schreier complexes; this proves it for the classes whose real part is pulled back from one fixed level, with a constant that depends on that level, and shows that the sufficient condition stated there is false as written.
  deligne-opnorm-monomial-models-are-almost-flat-circle-bundles: that gives the floor for Kahler-proportional classes, which are the classes pulled back from level one; this gives it for the classes pulled back from any fixed level, including non-Kahler, Eisenstein and boundary classes of a fixed congruence subgroup.
  deligne-parameter-group-is-a-virtual-invariant: that computes the virtual divisibility of the one Maslov class for general models; this bounds the virtual divisibility of every integral class of every finite-index subgroup, uniformly over all covers, by the finite profinite multiplier.
  deligne-monomial-cover-models-have-a-detecting-cycle-floor: that floor tends to 0 along towers because detecting cycles grow; this floor is constant along every tower above a fixed level.
---

**ESTABLISHED** (`deligne-third-floor-above-fixed-level-proof`). Unreviewed.

## Setting

The notation is that of `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles` ((L1)-(L3), (K1),
(K2)).
- `Gamma = Sp_4(Z)`. `Lambda_0 <= Gamma` has finite index, and `X_0 = Gamma / Lambda_0`.
- `pi : X' -> X_0` is a `Gamma`-map from a transitive `Gamma`-set `X' = Gamma / Lambda'`, with `Lambda' <= Lambda_0`.
- `A_X := { c in H^2(Y_X; R) : c|S_X = 0 }`. By Hopf, `A_X = Hom(H_2(Lambda; Z), R) = H^2(Lambda; R)`.
- `L_X` is the image of `H^2(Y_X; Z)` in `H^2(Y_X; R)`.
- `G_0 := H^2_cts(Lambda_0^, Q/Z)` is the profinite multiplier. It is finite by
  `sp4-finite-index-fd-projective-multiplier-is-finite`.

## Statement

**(F1) Bounded refinement.** There is a lattice `M(Lambda_0) <= A_(X_0)` with the following properties:
- it contains `L_(X_0) cap A_(X_0)`, with index at most `|G_0|`;
- it depends only on `Lambda_0`;
- for every `pi` as above, `{ c in A_(X_0) : pi^* c in L_(X') }` lies in `M(Lambda_0)`.

**(F2) Fixed-level floor.** Put `nu(Lambda_0) := min { ||c||_(cell, X_0) : 0 != c in M(Lambda_0) }`. It is
positive. Take any `pi` as above and any `f in kappa_(X') + 3 H^2(Y_(X'); Z)` with `f|S_(X') = 0` and
`f_R in pi^* A_(X_0)`. Then

```text
||f_R||_(cell, X') >= nu(Lambda_0).
```

By (L1), such classes can never push `mu_(1/3)(X')` below `nu(Lambda_0) / 3`, however far up the tower `X'` lies.
For `Lambda_0 = Gamma` this is the Kahler case of (K2), because `A_Y = R kappa_R`.

**(F3) Virtual divisibility is bounded.** Let `u in H^2(Lambda_0; Z)` with `u_R != 0`. Suppose that for some
finite-index `Lambda' <= Lambda_0`,

```text
res u in m H^2(Lambda'; Z) + torsion.
```

Then `u_R / m in M(Lambda_0)`. So `m` is bounded in terms of `u` and `Lambda_0` alone.

**(T) The stated sufficient condition is false.** The floor node proposes a uniform circle cosystole: for all `X`
and all integral `u` on `Y_X` with `u|S_X = 0` and `u` nonzero mod 3, `||u_R||_cell >= c`. This fails at
`Lambda = Gamma(3)`. There is a torsion class `t in H^2(Y_X; Z)` with `t notin 3 H^2(Y_X; Z)`, `t|Z_2 = 0` and
`t_R = 0`.

The repaired condition asks only for `u(Z_2(Y_X; Z))` not contained in `3Z`. It still implies the floor node with
(K1), since `f(Sigma) = D mod 3` by (L3). By (F3), no divided pullback of a fixed class can refute it.

## What this kills

**The named invariant** is the profinite multiplier `H^2_cts(Lambda_0^, Q/Z)`.

**The class of approaches.** Any attempt to refute the floor by refining a fixed level is dead. Such an attempt
takes classes of one fixed `Lambda_0` and pulls them up a tower of covers, dividing wherever the pullback becomes
divisible. The classes may be Kahler, Eisenstein, boundary or non-Kahler interior classes. This is the `T^2`
mechanism named in the floor node.

**Where every member dies.** Suppose `pi^* u = m w + (torsion)`. The torsion dies on a further finite-index
subgroup. So `u mod m` is virtually zero, and in degree 2 that means it is inflated from a finite quotient. Then
`u (x) 1/m` lies in the image of the finite group `G_0`.

**Calibration.** For `Z^2`, `H^2(Z^2^, Q/Z)` contains `Q/Z`, and the refinement is unbounded: the fundamental
class pulls back to `N^2` times a generator. For `Sp_4(Z)` the corresponding group is finite. The reason is
`b_2(sp_4) = 0`, through Lazard, as in the imported node.

## What is left

Any counterexample `(X_n, f_n)` with `||f_n||_cell -> 0` must be carried by classes that are new at every level.
- Fix any `Lambda_0` and suppose infinitely many `X_n` lie over `X_0`.
- Once `||f_n|| < nu(Lambda_0)`, `(f_n)_R notin pi_n^* A_(X_0)`.

The open problem is uniformity over the level. Along a cofinal tower `Lambda_j`, show that
`inf_j nu'(Lambda_j) > 0`. Here `nu'` is `nu` restricted to classes congruent to `kappa` mod 3 and new at level
`j`. This uniformity is exactly what the floor node still needs; (F2) gives each `nu'(Lambda_j) > 0` but no
bound in `j`.

The parallel w14 lane (swarm-0917-w14-w14-deligne-break) shows that no linear or character certificate can prove the
floor. Together, these two results mean a proof must be non-linear and must control new classes uniformly in the
level.
