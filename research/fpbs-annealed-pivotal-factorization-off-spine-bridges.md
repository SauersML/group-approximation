---
rg: 2
id: fpbs-annealed-pivotal-factorization-off-spine-bridges
kind: claim
title: In a quenched Bernoulli product over a label-independent environment, every annealed pivotal term factorizes with constant 2 except pivotals bridging two spine pieces, and in spine-augmented volumes the whole Russo part factorizes while the activation part is at most the Bernoulli-sandwiched spine two-point increment
distinct_from:
  fpbs-quenched-bk-russo-collapse-operator-gate: that proves the quenched diagram bound d tau^M/dr <= tau^M J tau^M and isolates the annealing inequality (G); this proves that annealing the pivotal part costs only a factor 2, because off bridges one quenched factor is a pure Bernoulli kernel, and bounds the activation part by an explicit fully annealed kernel
  fpbs-continuous-activation-collapse-family: that proves (G) fails in its density term; this splits that density into a Russo part, which factorizes with C = 2 uniformly in the volume, and an activation part, which carries the whole failure
  fpbs-spine-increment-activation-gate: that is the reduced gate and its failure for collapse families; this is the factorization and the activation bound it rests on
---

**ESTABLISHED.** Proof in
`fpbs-annealed-pivotal-factorization-off-spine-bridges-proof`.

**Setting.** `G` is a locally finite graph of maximal degree `d` (with
multiplicity), `J` its adjacency matrix, `xi_r = {e : U_e <= r}` with i.i.d.
uniform labels `U`. A *label-independent environment* is a nondecreasing
family `(Z_r)_{r in [t_0,t_1]}` of random edge sets, measurable with respect
to some `M` independent of `U`. Put `omega_r = xi_r ∪ Z_r`. Given `M`, the
edges are independent, `e` is open with probability `1` if `e in Z_r` and
`r` otherwise: this is the quenched product `P^M_r`. The environment is
*connected* if the graph `(V(Z_r), Z_r)` is connected (or empty) for every
`r`. The continuous-activation family of
`fpbs-continuous-activation-collapse-family` is a connected
label-independent environment on `[p_c,1]`, with `Z_{p_c} = ∅`.

For a finite edge set `Lambda`, `W = V(Lambda)`,
`T^Lambda_r(u,v) = P(u <-> v in omega_r ∩ Lambda)`, and
`beta^Lambda_r(u,v) = P(u <-> v in xi_r ∩ Lambda)` is the Bernoulli kernel.
All kernels have unit diagonal. The annealed off-spine Russo part is

```text
R^Lambda_r(u,v) = E[ sum_{f in Lambda \ Z_r} P^M_r(f is pivotal for u <-> v in omega_r ∩ Lambda) ].
```

**Theorem 1 (factorization off bridges).** For every label-independent
environment, every finite `Lambda`, every `r` and all `u,v`,

```text
R^Lambda_r <= T^Lambda_r J beta^Lambda_r + beta^Lambda_r J T^Lambda_r + Br^Lambda_r
           <= 2 T^Lambda_r J T^Lambda_r + Br^Lambda_r   (entrywise).
```

Here `Br^Lambda_r(u,v)` is the annealed mass of *bridging* pivotals: `f` is
pivotal, and after closing `f` the clusters of `u` and of `v` both meet
`V(Z_r ∩ Lambda)`. A bridging pivotal joins two distinct components of the
graph `Z_r ∩ Lambda`, so `Br^Lambda_r(u,v) = 0` on the event that
`Z_r ∩ Lambda` is connected. The constant `2` does not depend on `Lambda`, `r`
or the environment. So annealed pivotal factorization holds, with `C ≡ 2`,
for every pivotal that does not bridge two spine pieces. The only
non-factorizing pivotals are finite-volume artifacts of cutting a connected
spine.

**Spine-augmented volumes.** For finite `Lambda`, `u,v in W`, put

```text
X^Lambda_r(u,v) = P(u <-> v in omega_r ∩ (Lambda ∪ Z_r)),        S_r(x,y) = P(x,y in V(Z_r)),
```

so `X^Lambda` is a nondecreasing family of `W × W` matrices with unit
diagonal, and `S_r(x,x) = P(x in V(Z_r))` is the spine density. For
`s < t` split the increment exactly as

```text
X_t - X_s = D^R_{s,t} + D^A_{s,t},
D^R_{s,t} = E[ Phi(t; Z_t) - Phi(s; Z_t) ],   D^A_{s,t} = E[ Phi(s; Z_t) - Phi(s; Z_s) ],
Phi(r; Z)(u,v) = P(u <-> v in (xi_r ∪ Z) ∩ (Lambda ∪ Z))   (Z frozen).
```

`D^R` is the off-spine Russo part with the environment frozen, and `D^A >= 0`
is the activation part.

**Theorem 2 (the split in spine-augmented volumes).** For every connected
label-independent environment, every finite `Lambda` and all
`t_0 <= s < t <= t_1`, entrywise on `W × W`:

```text
(R)  D^R_{s,t} <= (t-s) (X_t J_W beta_t + beta_t J_W X_t) <= 2 (t-s) X_t J_W X_t,
(A)  D^A_{s,t} <= beta_s (S_t - S_s) beta_s,
```

with `beta = beta^Lambda`, `J_W` the restriction of `J`, and `S` compressed
to `W`. Hence

```text
X_t - X_s <= 2 (t-s) X_t J_W X_t + beta_s (S_t - S_s) beta_s .
```

Bridges cannot occur, because the whole connected spine lies in the volume.
The Russo part therefore factorizes with the constant `2`, uniformly in
`Lambda`. The activation part is bounded by an explicit, fully annealed
kernel: a Bernoulli connection to a vertex `x`, a spine two-point increment
from `x` to `y`, and a Bernoulli connection from `y`. No quenched
correlation between the two sides survives.

**Answer to the question of `fpbs-continuous-activation-collapse-family`.**
Annealed pivotal factorization holds: the off-spine Russo part satisfies
`R_r <= 2 T J T` up to bridges in plain volumes, and `D^R <= 2 (t-s) X J X`
exactly in spine-augmented volumes. The gate of
`fpbs-quenched-bk-russo-collapse-operator-gate` survives in these volumes
(`fpbs-spine-increment-activation-gate`, Theorem 1). So the non-integrable
density found there is carried entirely by activation. Its only annealed
input is the spine increment `beta (S_t - S_s) beta`.

**What is not decided.** Whether `Br^Lambda_r <= C(r) T J T` holds uniformly
over plain volumes is left open. It is not needed, because the gate only
uses one exhaustion and the spine-augmented exhaustion has no bridges.
