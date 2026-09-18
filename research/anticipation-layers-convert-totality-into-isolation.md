---
rg: 2
id: anticipation-layers-convert-totality-into-isolation
kind: claim
title: An anticipation layer (a label copied along a locally readable step map and fixed at terminal sites) is forced exactly where every step orbit terminates, so a seed lifts to a unique isolated point displaying its computed outputs iff the computation is total; the layer is quantum rigid on the terminating part, but two far-apart non-terminating basins in any configuration destroy rigidity
requires:
  - quantum-rigid-subshifts-cluster-the-modifications-of-each-point
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
distinct_from:
  quantum-rigid-subshifts-cluster-the-modifications-of-each-point: that is the general far-modification lemma; this applies it to one construction, the anticipation layer, where the modifications are flips of whole non-terminating basins, and adds the positive half (forcing and rigidity where orbits terminate).
  deterministic-time-lifts-inherit-quantum-rigidity: that lifts rigidity along a deterministic time direction with a base at every time; here the label is determined by the FUTURE of a walk, which is forced only when the walk terminates, so it is the mechanism by which totality, not determinism, is consumed.
  relative-seeds-glue-graphs-of-groups-into-class-c: that makes the forced point of a relative seed a membership oracle; this shows how a total computation can be written onto a seed while keeping it isolated, and why that alone never changes a stabilizer.
---

**ESTABLISHED** (lane proof, bh-invent-18, 2026-09-18; elementary; **not reviewed**; no priority
claimed). Quantum families and `D`-quantum rigidity are (Q1)–(Q3) of
`fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Setting

- `A` is a finitely generated group with finite symmetric generating set `S`, and `Y_0 ⊆ Σ^A` is an
  SFT with `(g.y)(h) = y(g^{-1}h)`. The *`r`-pattern of `y` at `q`* is `f ↦ y(qf)`, `f ∈ B_r`.
- **Step rule.** `σ : Σ^(B_r) → S ∪ {⊥}`. In `y`, the site `q` is *terminal* if `σ` of its pattern is
  `⊥`; otherwise its *successor* is `s_y(q) = q·σ(...)`.
- **Terminal type.** `θ : Σ^(B_r) → T`, with `T` finite and `|T| ≥ 2`.
- **Anticipation layer.** `Y = Y_0 ⋉_(σ,θ) T` is the set of pairs `(y, τ)`, `τ ∈ T^A`, such that:
  - `τ(q) = τ(s_y(q))` at non-terminal `q`;
  - `τ(q) = θ(r-pattern of y at q)` at terminal `q`.

  These rules have radius `r + 1`, so `Y` is an SFT, and it is `A`-invariant.
- **Orbits and basins.** The *orbit* of `q` in `y` is `q, s_y(q), s_y^2(q), …`. It *terminates* if it
  reaches a terminal. Two non-terminating orbits are equivalent if they eventually meet. A
  *non-terminating basin* is the set of sites whose orbits lie in one class.
  - A basin is closed under `s_y` and under `s_y`-preimages, and it contains no terminal.

## Theorem

1. **Forcing.** For `y ∈ Y_0` the fibre `{τ : (y, τ) ∈ Y}` is nonempty. It is a single point iff every
   orbit of `y` terminates. Otherwise the constant value of `τ` on each non-terminating basin can be
   changed independently.
2. **Isolation from totality.** Let `(Y_0, π)` have seed cylinder `{y_*}` (a seed or relative seed).
   Then `(Y, π × ∗)` has a one-point seed cylinder iff every orbit of `y_*` terminates. In that case:
   - the point is `(y_*, τ_*)` with `τ_*(q) = θ(terminal reached from q)`;
   - its stabilizer is `Stab(y_*)`;
   - `τ_*` is computable from `y_*` by running the walks.
3. **Quantum transport.** Suppose `Y_0` is `D`-quantum rigid over `k`, let `D' ≥ max(D, r + 1)`, and
   take a `D'`-quantum family for `Y`. Write:
   - `𝔅` for the (commutative) algebra of its base letters;
   - `F_t(q)` for its `T`-letters;
   - `P_s(q) ∈ 𝔅` for "the step at `q` is `s`";
   - `Π = P_(s_1)(q) P_(s_2)(qs_1) ⋯ P_(s_k)(qs_1⋯s_(k−1))` for a path word.

   Then `F_t(q)` commutes with `Π`, and `F_t(q) Π = Π F_t(qs_1⋯s_k)`. If the path ends at a terminal,
   `F_t(q) Π ∈ 𝔅`. So all `T`-letters lie in `𝔅` on the projection "the orbit from `q` terminates".
4. **Bounded computation is rigid and adds nothing.** Suppose no configuration of `Y_0` has a
   non-terminating orbit. Then:
   - orbit lengths are bounded by some `L`;
   - `Y` is `D'`-quantum rigid for `D' ≥ max(D, (L+1) r + 1)`;
   - `τ` is a function of the `(L+1)r`-pattern of `y`.
5. **Unbounded computation must converge.** If `Y` is `D`-quantum rigid over some field, then in every
   `y ∈ Y_0` any two non-terminating basins are at distance `≤ 2D`.
   - If the orbit lengths of `y_*` are unbounded, then `Y_0 ⊇ \overline{A.y_*}` contains configurations
     with non-terminating orbits (König). So item 5 is a real constraint on every seed that computes
     beyond bounded look-ahead.

## Proof

**1.**
- *Existence.* Put `τ(q) = θ(terminal of q)` on terminating sites, and a constant per non-terminating
  basin. The rules hold because the step map preserves both kinds of site.
- *Uniqueness.* If every orbit terminates, induct on the distance to the terminal.
- *Non-uniqueness.* Changing the constant on one basin breaks no rule. No rule links a site of the basin
  to a site outside it: if `s_y(q)` lies in the basin, so does `q`. And the basin has no terminals. `∎`

**2.** A point of the cylinder has base `y_*` (its first coordinate carries `π`), and by 1 its label is
forced iff `y_*` is total. If `g.(y_*, τ_*) = (y_*, τ_*)` then `g.y_* = y_*`. Conversely, `g ∈ Stab(y_*)`
maps the unique lift to a lift of `y_*`, which is the same point. `∎`

**3.**
- **The base letters commute.** They form a `D'`-quantum family for `Y_0`. Expanding a non-occurring
  `Y_0`-pattern into `Y`-patterns gives only non-occurring patterns. By monotonicity in `D`, `Y_0` is
  `D'`-rigid, so the base letters commute.
- **One step.** For `t ≠ t'`, the event "step `s` at `q`, `τ = t` at `q`, `τ = t'` at `qs`" occurs in
  no point of `Y`.
  - Expanding it over the `D'`-ball gives `P_s(q) F_t(q) F_(t')(qs) = 0` by (Q3). All factors commute by
    (Q2), since they sit within `r + 1` of `q`.
  - Summing over `t'` gives `P_s F_t(q) = P_s F_t(q) F_t(qs)`, and symmetrically
    `P_s F_t(qs) = P_s F_t(q) F_t(qs)`.
  - So `P_s(q) F_t(q) = P_s(q) F_t(qs)`.
- **Induction** along the path, using only these one-step identities and commutation inside `𝔅`:
  - `F_t(q) P_1 ⋯ P_k = P_1 F_t(q_1) P_2 ⋯ P_k = … = P_1 ⋯ P_k F_t(q_k)`;
  - `P_1 ⋯ P_k F_t(q) = P_2 ⋯ P_k P_1 F_t(q_1) = … = P_1 ⋯ P_k F_t(q_k)`, reordering `P`'s inside `𝔅`.

  The two lines together give `F_t(q) Π = Π F_t(q) = Π F_t(q_k)`.
- **At a terminal**, the same argument with the terminal rule gives
  `P_⊥(q_k) F_t(q_k) = P_⊥(q_k) Θ_t(q_k)`, where `Θ_t ∈ 𝔅` is "terminal of type `t`". `∎`

**4.**
- **The bound.** The closed sets "the orbit of `1` has length `> k`" decrease with `k`, and their
  intersection is empty. By compactness one of them is empty, and equivariance gives the same bound at
  every site.
- **The projections vanish.** Every pattern on `B_((L+1)r)(q)` whose walk from `q` does not terminate
  within `L` steps occurs in no point of `Y_0`. By (Q3) at scale `D'` its projection is `0`. So the
  terminating path projections sum to `1`.
- **Conclusion.** By 3, every `F_t(q)` is a finite sum of elements of `𝔅`. `∎`

**5.**
- **The two points.** Fix `y` and two non-terminating basins `Δ_1, Δ_2` with `d(Δ_1, Δ_2) > 2D`. Let
  `x = (y, τ)`, and let `y_i` flip the value of `τ` on `Δ_i`. By 1 these lie in `Y`, and
  `Δ(x, y_i) = Δ_i`.
- **The lemma.** Lemma 1 of `quantum-rigid-subshifts-cluster-the-modifications-of-each-point` then
  gives non-rigidity at scale `D`.
- **The König remark.** If the orbit lengths of `y_*` are unbounded, choose `g_n` with the orbit of `1`
  in `g_n.y_*` longer than `n`. Any limit point has a non-terminating orbit at `1`. `∎`

## Examples and calibration

- **Product geometry kills anticipation even when the output is trivial.**
  - *The layer.* Over `Z²` with `C_Z × C_Z`, let every site step down until it reaches the flip row
    of the vertical coordinate, and let `θ` read the horizontal sign there.
  - *The seed.* In the seed point every walk terminates, and `τ_*(i, j) = sign(i)`, which is already
    readable in the base.
  - *The failure.* In the boundary point whose vertical flip row is at `−∞`, every column is its own
    non-terminating basin. By 5 the layer is not rigid at any scale.
  - *Why.* Parallel walks never approach each other. This is the space-wall failure of time lifts
    (`deterministic-time-lifts-inherit-quantum-rigidity`) seen from the future side.
- **Tree geometry is compatible with 5.** Walks toward an end merge. In the flows of
  `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`, there is at most one non-terminating
  basin in each point.
- **Machine walks are at risk.** Walks that simulate a counter or Turing machine from distinct inputs
  typically neither merge nor stay close. Whenever limits of long runs produce two such runs far apart
  in one boundary point, item 5 kills rigidity at every scale, whatever the base. This is a condition
  to check for each design, not a theorem about all machines.

## What this means for (SEED) and CAP (SYNTHESIS v6, gate 1)

- **Where decidability is consumed.** Item 2 is the exact form of "the non-local constraint uses the
  input's decidability". A label fixed by the outcome of a walk is locally checkable, and it is forced
  on a seed iff the walk halts from every site. Totality of the decision procedure *is* isolation of
  the decorated seed. No local rule can see it.
- **What anticipation cannot do.** By item 2 it never changes a stabilizer. It displays computed values
  on a seed, but it cannot create a relative seed with hard membership. The membership oracle of
  `relative-seeds-glue-graphs-of-groups-into-class-c` item 3 must already be carried by the base
  geometry.
- **The rigidity price.** Unbounded computation leaves non-terminating walks in the boundary (5, König),
  and rigidity forces them to converge. In amenable and product geometry, parallel walks stay apart, so
  rigid anticipation has bounded look-ahead there (items 4 and 5). Only tree-like, converging flows
  survive.
- **The decisive lemma of this mechanism (CB), OPEN.** Find a rigid seed `(Y_0, y_*)` over a finitely
  presented group, together with a total walk rule on `y_*`, such that:
  - its outputs lie outside every fixed complexity class;
  - in every point of `Y_0`, any two non-terminating basins come within bounded distance.

  - *What CB gives.* CB would show that rigid seeds can carry arbitrary total computations, which is
    what any use of seeds as certificates needs.
  - *What it does not give.* By item 2 it leaves the group and its word problem unchanged, so it does
    not by itself decide CAP.
  - *Evidence.* The examples above suggest that convergence and computation pull against each other,
    and bh-star-a should weigh that for CAP.

## Lesson for general BH

A total algorithm can be written onto a seed by a locally checkable anticipation layer: a label
copied along a walk and fixed where the walk halts. The decorated seed stays isolated exactly because
the algorithm halts everywhere, so decidability is spent as isolation. Rigidity, however, is paid for
by convergence. Every unbounded computation leaves non-terminating walks in the boundary, and two of
them far apart are two far modifications, which the clustering lemma forbids. So rigid seeds can carry
computation only along flows that merge (tree-like compression). In product or amenable geometry they
carry none beyond bounded look-ahead, and even there a non-convergent walk kills rigidity although it
computes nothing. The positive route now has one precise target (CB). Its tension, "merge versus
compute", is the concrete form of the CAP question for seed decorations.
