---
rg: 2
id: vertex-orbit-finite-a-sets-are-rooted-trees-or-finite
kind: claim
title: Genuine SL2(Z[1/p])-sets with finite vertex-group orbits are finite with collapsed charts or rooted trees whose orbit windows lose (p-1)/(p+1) of their mass
distinct_from:
  dyadic-radial-shell-couplings-have-one-third-boundary: that treats finite mixtures of genuine tree spheres, whose stabilizers are congruence subgroups inside one vertex group; this treats every genuine A-set whose vertex-group orbits are finite, with arbitrary (non-congruence, non-normal) stabilizers, at every prime, and proves those are the only two kinds.
  homogeneous-k-orbit-factor-has-no-finite-a-refinement: that excludes exact finite refinements of the K-orbit factor of a compact quotient; this classifies all countable A-sets with finite vertex orbits and bounds the window mismatch of their infinite orbits.
  expanding-matchings-need-a-shared-stabilizer: that is a spectral bound for bijections between congruence vertex models; this is a combinatorial bound for identity couplings inside one genuine A-set, and it needs no congruence or expansion hypothesis.
  dyadic-amplified-edge-random-lifts-exist: that asks for Hamming-almost couplings of arbitrary exact vertex actions; this refutes only the construction that takes both vertex actions from one genuine A-set and matches orbit windows by the identity.
---

**ESTABLISHED (unreviewed).** Let `p` be a prime, `A = SL_2(Z[1/p])`, `L = SL_2(Q_p)` and `T` the
`(p+1)`-regular Bruhat--Tits tree. `A` acts on `T` without inversions. Let `v_0, v_1` be adjacent
vertices with `C_0 = Stab_A(v_0) = SL_2(Z)`, `C_1 = Stab_A(v_1)` and `B = C_0 ∩ C_1`, so that
`A = C_0 *_B C_1` and `[C_j : B] = p+1`. Write `C^v = Stab_A(v)`.

**(V1) Dichotomy for stabilizers.** Let `D <= A` be such that `D ∩ C^b` has finite index in `C^b`
for some vertex `b`. Then exactly one of the following holds.
- `D` fixes a vertex of `T`.
- `[A : D] < ∞`, and `C_0` and `C_1` each act transitively on `A/D`.

The proof uses no congruence subgroup property, only the Cartan decomposition and unipotent
contraction in `L`.

**(V2) Window mismatch.** Let `X` be an A-set in which every `C_0`-orbit is finite and no A-orbit is
finite. Let `P_0` be a finite union of `C_0`-orbits and `P_1` a finite union of `C_1`-orbits. Then

```text
|P_0 Δ P_1|  >=  ((p-1)/(p+1)) · (|P_0| + |P_1|).                      (VW)
```

At `p = 2` this is `|P_0 Δ P_1| >= (|P_0|+|P_1|)/3`, the same constant as the radial-shell firewall.

**(V3) Charts collapse on finite orbits.** On a finite A-orbit, `C_0`-orbit = `C_1`-orbit =
A-orbit. So the normal-form blocks `Orb_(C_0)(r_x^(-1) ω)` of
`dyadic-amplified-edge-random-lifts-exist` coincide for all `x`.

## What this kills

Consider every coupling built as follows. Take a genuine A-set `X` with finite vertex-group orbits,
with any stabilizers at all. Take `Ω` to be a finite window, `ρ_0` the genuine `C_0`-action on a
union of `C_0`-orbits, and `ρ_1` the genuine `C_1`-action on a union of `C_1`-orbits, with the
identity as the matching.

- **The invariant.** It is the closure in `L` of the point stabilizer. By (V1) that closure is
  either compact or all of `L`.
- **Where every member dies.** If the closure is all of `L`, the window is a finite orbit and the
  charts collapse (V3). If it is compact, `D\T` is a rooted tree. Every parent edge then carries
  exactly `1/(p+1)` of its child's mass, and (VW) forces a mismatch of at least `(p-1)/(p+1)` of
  the mass.

In particular non-congruence stabilizers give no escape from the radial-shell firewall. Every
non-congruence stabilizer with finite vertex orbits either lies inside a vertex group (a rooted
tree, so the bound applies) or has finite index (so the charts collapse). A positive construction
for `dyadic-amplified-edge-random-lifts-exist` must re-glue at least a `(p-1)/(p+1)` share of the
points by structure coming from no genuine A-set.

**Projective version.** The central `±1` acts trivially on `T`. So everything above holds verbatim
for `PSL_2(Z[1/p])` acting on sets, applied to the preimages of the stabilizers.

**Scope.** This does not bound Hamming-almost intertwiners between vertex actions taken from
different A-sets, or between arbitrary exact vertex actions. That is the open content of
`dyadic-amplified-edge-random-lifts-exist`.

DERIVATION
vertex-orbit-finite-a-sets-are-rooted-trees-or-finite-proof
