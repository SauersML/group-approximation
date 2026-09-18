---
rg: 2
id: fpbs-volume-uniform-activation-gate-log-law
kind: claim
title: Any activation gate that holds uniformly over finite spine-augmented volumes, already over two-edge volumes, needs mass at least c log(m(t)/m(s)) on (s,t], so it fails at the birth of every connected invariant spine, whether or not the family collapses
distinct_from:
  fpbs-spine-increment-activation-gate: that proves (AG) fails along every exhaustion for collapse families, by contradiction with collapse and without a rate; this proves a quantitative log law for the volume-uniform form of (AG), from two-edge test volumes, for every connected invariant spine grown from the empty set, and uses no collapse, uniqueness or critical-L2 input
  fpbs-continuous-activation-collapse-family: that shows the uniform-in-volume density ratio C* is not integrable for one collapse family, again by contradiction; this gives the explicit lower bound c log(m(t)/m(s)) for the activation part alone, for every such environment
  fpbs-annealed-pivotal-factorization-off-spine-bridges: that bounds the activation part D^A from above by beta (S_t - S_s) beta; this bounds D^A from below on two-edge volumes and compares it with X J X from above
---

**ESTABLISHED (class-killing obstruction; the log law).** Proof in
`fpbs-volume-uniform-activation-gate-log-law-proof`.

**Setting.** As in `fpbs-annealed-pivotal-factorization-off-spine-bridges`.
`G = Cay(Gamma,S)`, `d = |S|`, `J` the adjacency matrix and
`mu = max_{a ≠ b} J(a,b) <= d` its largest off-diagonal entry. `xi_r` is
Bernoulli(`r`) bond percolation built from i.i.d. uniform labels `U`.
`(Z_r)_{r in [t_0,t_1]}` is a nondecreasing family of random edge sets,
measurable with respect to some `M` independent of `U`, with `t_0 > 0`.
We assume:

* **(E1) invariant.** The joint law of `(Z_r)_r` is `Gamma`-invariant;
* **(E2) connected and infinite.** Almost surely, for every `r`, `Z_r` is empty
  or a connected graph with infinitely many vertices;
* **(E3) continuous density.** `m(r) = P(o in V(Z_r))` is continuous on `[t_0,t_1]`.

The continuous-activation family of `fpbs-continuous-activation-collapse-family`
satisfies (E1)-(E3) on `[p_c,1]` with `m(p_c) = 0`: (E1) and (E2) are Steps 3
and 5 of its proof, and (E3) holds because every activation time has an
atomless law ((C3)). For a finite edge set `Lambda` with `W = V(Lambda)`, the
spine-augmented kernel `X^Lambda_r`, the activation part `D^A_{s,t}` and the
restricted adjacency `J_W` are as there.

**Volume-uniform gate.** A finite Borel measure `kappa_A` on `(t_0,t_1]`
satisfies **(AG_unif)** on a class `𝓛` of finite edge sets if

```text
D^{A,Lambda}_{s,t} <= kappa_A((s,t]) X^Lambda_t J_W X^Lambda_t   entrywise on W × W,
for all Lambda in 𝓛 and all t_0 <= s < t <= t_1 .
```

Let `𝓛_2` be the class of two-edge sets `{e_1,e_2}` whose endpoint pairs are
at graph distance at least `2` from each other.

**Theorem 1 (two-edge ratio bound).** Let `Lambda = {e_1,e_2} in 𝓛_2`, with
`e_1 = {u,w}` and `e_2 = {v,w'}`, and put

```text
Psi(r) = P( {u,w} ∩ V(Z_r) ≠ ∅  and  {v,w'} ∩ V(Z_r) ≠ ∅ ).
```

Then, for all `t_0 <= s < t`, assuming only (E2),

```text
s^2 (Psi(t) - Psi(s)) <= D^A_{s,t}(u,v),        (X_t J_W X_t)(u,v) <= 4 mu Psi(t).
```

Hence every `kappa_A` satisfying (AG_unif) on `{Lambda}` has
`kappa_A((s,t]) >= (s^2 / (4 mu)) (1 - Psi(s)/Psi(t))` whenever `Psi(t) > 0`.

**Theorem 2 (log law).** Assume (E1)-(E3) and let `kappa_A` satisfy (AG_unif)
on `𝓛_2`. Then for all `t_0 <= s < t <= t_1` with `m(s) > 0`,

```text
kappa_A((s,t]) >= (t_0^2 / (8 mu)) · floor( log(m(t)/m(s)) / log(4 d^4) )
               >= c log(m(t)/m(s)) - t_0^2/(8 mu),        c = t_0^2 / (8 mu log(4 d^4)).
```

The same bound holds for (AG*) on `𝓛_2`, and for the full gate
`X_t - X_s <= kappa((s,t]) X_t J_W X_t`, since each of these implies
(AG_unif) with `kappa_A` replaced by the respective measure.

**Corollary 3 (birth of a spine).** Assume (E1)-(E3), `Z_{t_0} = ∅` and
`Z_{t_1} ≠ ∅` with positive probability. Then no measure `kappa_A` that is
finite on `(t_0,t_1]` satisfies (AG_unif) on `𝓛_2`. The same is true of (AG*)
and of the full gate. Indeed, with `s* = max{r : m(r) = 0}` and `s ↓ s*`,
Theorem 2 gives `kappa_A((s*,t_1]) = infinity`.

**What this kills.** Corollary 3 uses no uniqueness, no collapse, no critical
L2 bound and no property of `xi` beyond independence from `M`. So it applies
to every connected invariant spine born from nothing, whether or not
`omega_t = xi_t ∪ Z_t` is a collapse family. Any input that controls the
activation part by `X J X` *uniformly over finite spine-augmented volumes*
is therefore impossible, and its failure carries no information about
uniqueness. The failure is also quantitative: the uniform rate grows like
`d log m`. That turns the heuristic `∫ dS/S = infinity` of
`fpbs-spine-increment-activation-gate` into a theorem for the volume-uniform
form of the gate.

Such an input can only be exhaustion-specific. It would have to use the
growth of `X^{Lambda_j} J X^{Lambda_j}` in large volumes, which is where the
two-edge test volumes are cheap and large volumes are not. So the gate of
`fpbs-spine-increment-activation-gate`, Theorem 1, which needs only one
exhaustion, is the correct form. Its failure for collapse families, and not
this log law, is the substantive obstruction.

**What is not decided.** Whether the log law holds along a fixed exhaustion
`Lambda_j`. In a large volume, `X_t J X_t(u,v)` contains the spine-routed mass
`sum_{a~b} X_t(u,a) X_t(b,v)`, which is unbounded as the volume grows. So the
two-edge mechanism does not transfer to an exhaustion. A sparse exhaustion
might need only mass of order the number of volume scales between `m(s)` and
`m(t)`.
