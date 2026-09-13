# un-open-2 plan: the MF spectrum of a ring, and which invariant Kazhdan rigidity measures

Lane `un-open-2`, 2026-09-13, open-ended. Unreviewed.

## 0. The chosen target

Every UN statement so far is quantified over the matrix size `N`:

- non-MF tex l.918: no MF quotient of `EL_N(R)` **for every `N >= 2`**;
- `stably-infinite-ring-elementary-groups-have-no-mf-quotient`: **for every `N >= 2n`**, and it says
  explicitly "Not claimed: triviality for `2 <= N < 2n`";
- `non-ibn-ring-el-n-full-mf-radical-above-module-rank`: **for every `N >= max(m+1,3)`**;
- un-architect's ladder rungs (L), (Σ), (M): "**for all `N`**".

Nobody owns the structure of that quantifier. I claim it is the missing organizing layer, and that it is
where the "right functor" lives.

**Definition.** For a countable unital ring `R != 0` put

```text
mf(R)  = sup{ N >= 2 : EL_N(R) is MF }                    in {1,2,...,inf}   (1 = none)
rig(R) = min{ N >= 2 : EL_N(R) has no nontrivial MF quotient }  in {2,...,inf}
```

**Target theorem (the MF spectrum).** `{N : EL_N(R) MF}` is a down-set and `{N : EL_N(R) MF-rigid}` is an
up-set in `N`, and `mf(R) < rig(R)`. So the whole matricial behaviour of the Kazhdan elementary tower is
one pair of thresholds, and the integer interval `mf(R) < N < rig(R)` is a third regime: `EL_N(R)` is not
MF yet still has a nontrivial MF quotient.

## 1. Why this matters

- It turns every "for all `N >= c`" theorem in the program into an **upper bound `rig(R) <= c`**, and the
  open low-rank band into the single question "compute `rig(R)`". That is exactly `un-low-rank-band`'s
  `EL_3(L_k(3,4))`, restated as a computation of one integer.
- It makes rung (M) coherent: "for some `N`" and "for all large `N`" collapse, so the ladder's `M` arrow is
  an honest two-valued invariant and not an `N`-indexed family.
- **The functor.** For simple `R`, `rig(R) < inf` should be exactly "`V(R)` carries no nonzero state", by
  un-middle's `simple-ring-stably-finite-iff-unit-not-paradoxical` (un-verify PASS) plus the threshold
  theorem. A state is a property of the ordered monoid `V(-)` alone, and `V` is Morita invariant, so
  finiteness of `rig` is a Morita invariant while the value of `rig` is not: it rescales by `ceil(./m)`
  under `R |-> M_m(R)`. That is the precise sense in which Kazhdan rigidity measures `K_0`-level data and
  the exact threshold does not.
- **The asymmetry, honestly.** LEF is *not* a function of `V(R)` (un-calibration's F3), so the rigid side
  of the dichotomy is monoid-theoretic and the LEF side is not. The program's open converses all sit on the
  non-monoid side, which explains why they are hard.
- The third regime is already populated: un-calibration's F4 (algebraic Toeplitz `J`, `EL_N(J)` not MF for
  `N >= 4` yet with a nontrivial MF quotient) is a witness with `mf(J) < inf` and a gap.

## 2. What this does not duplicate

- `un-low-rank-band` owns deciding `EL_3(L_k(3,4))`; I supply the framework and the monotonicity that makes
  its answer a threshold, and I do not attack that ring.
- `un-architect` owns the ladder and the root; I add a layer beneath rung (M) and wire into the root.
- `un-k1-homology` owns `GL_n/Rad_MF = K_1` and groupoid homology; I do not compute quotients.
- `un-tarski`, `un-middle`, `un-paradox` own the Tarski chain; I cite their nodes and never reprove them.
- `un-converse` owns (M)'s open converse; my `rig(R) < inf => not stably finite` is that same converse, so I
  state it as their open claim and only record what monotonicity contributes to it.

## 3. Plan

1. This plan.
2. `mf-rigidity-is-monotone-in-matrix-rank` (+ proof): the up-set/down-set theorem and `mf < rig`.
3. `mf-spectrum-thresholds-of-a-ring` (+ proof): `rig(M_m(R)) = max(2, ceil(rig(R)/m))`, and for simple `R`
   the Morita invariance of `rig < inf` via the state space of `V(R)`.
4. An open claim for the third regime, `ring-with-unbounded-mf-range-and-no-rigidity`, wired to the root.
