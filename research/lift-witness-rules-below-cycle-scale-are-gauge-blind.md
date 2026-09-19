---
rg: 2
id: lift-witness-rules-below-cycle-scale-are-gauge-blind
kind: claim
title: On a gauge-randomised linear source the orientation-lift value of any labelling rule whose acceptance functions carry no Fourier mass on the cycle code is the same on satisfiable and unsatisfiable orbits, so a witness rule of support below the source cycle scale turns completeness above one half into equal soundness
distinct_from:
  view-local-branch-selectors-are-gauge-blind: that bounds the honest lift value of an equivariant menu by one half and says nothing about non-honest labellings; this bounds nothing absolutely and instead equates the average over the satisfiable gauge orbit with the average over an unsatisfiable one, for arbitrary labellings, provided the rule that produces them reads fewer right-hand sides than the source cycle scale. The invariant there is the visible parity space of a selector view; here it is the Fourier mass of the edge-acceptance function on the cycle code of the whole source.
  view-local-selectors-beat-one-half-through-non-honest-witnesses: that asks whether some non-honest labelling family beats one half on YES instances; this shows that no such family produced by a rule of support below the cycle scale can do so and leave any soundness gap, so it prunes that hole's survivor space rather than deciding it.
  efficient-branch-selectors-list-decode-honest-outer-labels: that kills honest and near-honest witnesses for polynomial-time selectors, conditionally on NP not in RP, through Fourier list decoding of the outer labels; this is unconditional, covers witnesses that are arbitrarily far from honest, puts no computational bound on either the selector or the witness, and gets its obstruction from the gauge action of the source rather than from decoding.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that exhibits one explicit labelling, the gauge labelling F*, of value 1 on the branch-blind coarsening of every DKKMS instance; this shows that F*, and every other rule of small right-hand-side support, has the same lift value on satisfiable and unsatisfiable orbits, so it supplies the reason F* cannot separate rather than a labelling of a particular coarsening.
  orientation-lifts-sandwich-2to1-game-values: that computes the value window of a lift in terms of the source game value for a fixed instance; this compares two different instances over one coefficient matrix and needs the gauge action, not the value window.
artifacts:
  - experiments/ugc-witness-locality-2026-09-18/check_witness_locality.py
---

**ESTABLISHED.** Route: `lift-witness-rules-below-cycle-scale-gauge-blindness-proof`.

The proof is a Fourier identity for the gauge action plus a first-moment count,
and it is summarised below. The artifact checks the exact statement by
enumerating whole gauge orbits.

## Setting

**Source and gauge.** A 3LIN instance is `I = (M, b)` with `M` in `F_2^(m x n)`,
rows `m_j` of weight 3, and right-hand side `b` in `F_2^m`. For `z in F_2^n` the
gauge is `I^z = (M, b + M z)`. Imported verbatim from
`view-local-branch-selectors-are-gauge-blind`: "`A |-> A + z` maps the
assignments of `I` bijectively to those of `I^z` and satisfies exactly the same
equations. So `z -> I^z` is a polynomial-time map that preserves the value
exactly". Hence every coset of `Im(M)` in `F_2^m` is a set of instances of one
common 3LIN value; call it a **gauge orbit**. The orbit `Im(M)` is the orbit of
the satisfiable instances.

**Cycle code and cycle scale.** The **cycle code** of the source is
```text
C^perp(M) = ker(M^T) = { c in F_2^m : sum_(j in supp c) m_j = 0 },
```
the sets of equations whose left-hand sides cancel. Its minimum nonzero weight
is the **cycle scale** `d_cyc(M)`. A set `S` of equations is **cycle free** when
`(m_j)_(j in S)` are independent; every `S` with `|S| < d_cyc(M)` is cycle free.

**Locally gauged lifts.** A **locally gauged game** over `M` is a weighted game
`G(b)` whose vertex set, label sets, edge set and weights depend on `M` only,
and in which the constraint of an edge `e` depends on `b` only through
`(b_j)_(j in W_e)` for a set `W_e` that depends on `M` and `e` only. The folded
DKKMS Grassmann 2-to-1 instances and their orientation lifts are locally gauged.
Verbatim from `view-local-branch-selectors-are-gauge-blind`: "vertices,
subspaces and weights depend on `M` only" and "`b` enters only through the
folding offsets `h_U`". Verbatim from
`grassmann-composed-2to2-coarsenings-are-satisfiable`: "`h_U : H_U -> F_2` is
`h_U(x_e) = b_e`", the unfolding is "`u_i(sigma)(x) = sigma(r_i x) + h_(U_i)(x - r_i x)`",
and "The 3LIN right-hand sides enter only through the folding offsets `h_U`."
An agreement edge compares two unfolded labels, so `W_e = U_1(e) union U_2(e)`
and `|W_e| <= 2k`. A **view-local selector** `S` with views `J_e`, `|J_e| <= s`,
adds only its own dependence, so the orientation lift `U_(S(b))` is locally
gauged with
```text
T_e = W_e union J_e,      |T_e| <= 2k + s.
```

**Witness rules.** A **witness rule** is a map `W` from `F_2^m` to labellings of
the lift; `W(b)_p` is the label it gives vertex `p` on input `b`. It is
**`R`-local** when each `W(b)_p` depends on `b` only through `(b_j)_(j in N_p)`
with `|N_p| <= R` and `N_p` a function of `M` and `p` only. Write
`Val_b(W)` for the weight of the edges of `U_(S(b))` that `W(b)` satisfies, so
`Val_b(W) <= val(U_(S(b)))`. Let `f_e : F_2^m -> {0,1}` be the indicator that
`W(b)` satisfies edge `e`, and
```text
S_e = T_e union N_(p_1(e)) union N_(p_2(e)),     D(S, W) = max_e |S_e|.
```

**Cycle leakage.** For a pair `(S, W)`,
```text
Lambda(S, W) = sum_e w_e * sum_(0 != c in C^perp(M)) | hat f_e(c) |,
```
the total Fourier mass the edge-acceptance functions put on nonzero cycles. It
is the witness-side analogue of the parity leakage `w_bad` of
`view-local-branch-selectors-are-gauge-blind`.

## Theorem 1 (cycle-blind rules cannot tell the orbits apart)

For every `b, b'` in `F_2^m`,
```text
| E_z Val_(b + Mz)(W)  -  E_z Val_(b' + Mz)(W) |  <=  2 Lambda(S, W).
```
In particular, if `D(S, W) < d_cyc(M)` then `Lambda(S, W) = 0` and the average
lift value of `W` is **exactly the same on every gauge orbit**: on the
satisfiable instances and on every unsatisfiable coset alike.

## Theorem 2 (a local completeness witness is its own soundness witness)

Assume `Pr_z[ Val_(Mz)(W) >= 1/2 + gamma ] >= 1 - eta` on the satisfiable orbit.
Then for every `b`,
```text
Pr_z[ val(U_(S(b + Mz))) >= 1/2 + gamma/2 ]  >=  gamma - 2 eta - 4 Lambda(S, W).
```
So when `Lambda(S, W) < (gamma - 2 eta)/4`, a positive fraction of **every**
gauge orbit has lift value at least `1/2 + gamma/2`. If some orbit over `M`
consists of NO instances of gap-3LIN, the lift has no gap: its soundness is at
least `1/2 + gamma/2`.

## Theorem 3 (the hypotheses are simultaneously satisfiable)

For every `eps > 0` there are `C = C(eps)` and `delta > 0` and a 3LIN
coefficient matrix `M` with `m = C n` weight-3 rows such that, for all large `n`,
```text
d_cyc(M) >= delta n        and        at least half the cosets of Im(M)
                                       have 3LIN value <= 1/2 + eps.
```
So the theorem is never vacuous: over one and the same `M` there is a
satisfiable gauge orbit, there are NO orbits of gap-3LIN, and the locality
budget `D(S, W) < d_cyc(M)` is linear in `n`. A witness rule may read a constant
fraction of all right-hand sides and still die.

## Class kill

Consider any proof that a Grassmann orientation lift has completeness
`1/2 + gamma` on YES instances, which runs through these steps:

- (i) a view-local selector `S` with views of size `s`;
- (ii) a witness rule `W` that produces, for each instance on the gauge orbit, a
  labelling of value at least `1/2 + gamma`, honest or not;
- (iii) soundness `s_lift < 1/2 + gamma/2` inherited from the source game.

Every such proof needs `Lambda(S, W) >= (gamma - 2 eta)/4`. It dies at step (ii)
on the source of Theorem 3. **The invariant is the Fourier mass of the
edge-acceptance function on the cycle code `ker(M^T)`.** The step where every
member dies is the exact uniformity of `(b + Mz)|_S` for a cycle-free `S`, which
makes each edge's acceptance probability a function of `M` alone.

The kill applies to witnesses that are arbitrarily far from honest, to witness
rules that are not computable, and to selectors that are not efficient. What it
needs instead is that the rule's dependence on the right-hand sides be
cycle-blind.

**What has cycle leakage, and what has not.**

- The DKKMS gauge labelling `F*` of
  `grassmann-composed-2to2-coarsenings-are-satisfiable` is the folded zero
  label. Its unfolding `F*(z, M)(r) = h_U(r - pi_Q(r))` reads only the equations
  of its own window, so it is `O(k)`-local and `Lambda = 0`. **The canonical
  non-honest candidate is dead by Theorem 2.** The artifact measures this
  directly.
- The honest labelling of a satisfying assignment is *not* cycle blind, and the
  reason is exactly its honesty. A satisfying assignment is a global linear
  function `t_i = <u_i, b>` of the right-hand sides, the Fourier support of an
  edge acceptance lies in `Span({e_j : j in T_e} + {u_i : i in V_e})`, and for a
  window equation `j` with variables `V`, the vector `e_j + sum_(i in V) u_i`
  lies in `ker(M^T)`. That character is precisely the test "does `t` satisfy
  equation `j`". So honesty *is* cycle leakage; and
  `view-local-branch-selectors-are-gauge-blind` shows that even full cycle
  leakage of this shape caps the value at `1/2 + w_bad/2`.

**Decomposition of the surviving hole.** After this claim, a witness for
`view-local-selectors-beat-one-half-through-non-honest-witnesses` must satisfy
two independent necessary conditions, each of which can fail on its own:

- **(H2a)** cycle leakage `Lambda >= (gamma - 2 eta)/4`: the rule must read a
  parity cycle of the source, hence at least `d_cyc(M) = Omega(n)` right-hand
  sides, at some vertex;
- **(H2b)** it must not be an honest labelling drawn from an equivariant menu of
  size `exp(o(n/s^2))` (`view-local-branch-selectors-are-gauge-blind`,
  Theorem 2).

The only known cycle-leaking construction, the honest labelling, fails (H2b),
and the only known non-honest construction, `F*`, fails (H2a).

## Check

`python3 experiments/ugc-witness-locality-2026-09-18/check_witness_locality.py`,
default seed 20260918.

- `--mode main` builds a source with `n = 12`, `m = 14`, cycle scale
  `d_cyc = 8`, and an abstract locally gauged lift with 6 A-vertices, 6
  B-vertices, 12 edges and `max |S_e| = 5`. It enumerates all `2^12` gauges of
  each of the 4 cosets of `Im(M)` and computes exact averages. The zero rule
  (`F*`), the per-A-vertex greedy local maximiser and a random local rule each
  give **bit-identical averages on all four cosets**: `0.416667`, `0.622396`,
  `0.348958`. The greedy rule beats one half, so the equality is not vacuous.
  Two controls separate the cosets, as they must: a rule that reads one weight-8
  cycle (`0.416667` against `0.260417`), and, after duplicating an equation so
  that `d_cyc = 2`, a 2-local rule that reads both copies (`0.437500` against
  `0.302083`).
- `--mode decouple` checks over all `2^9` right-hand sides of a tiny instance
  that `val(U_o) <= sum_a max_sigma (branch score at a)`, with 0 violations, and
  that this decoupled bound is **vacuous** for the selector
  `g_e(view)(tau) := c_e(b)`: its minimum over all `b` is 1. See the route file
  for why that closes the decoupling attack.
- `--mode regime` measures the cycle scale at density `m = 2n`. It is 4 up to
  `n = 80` and above 6 at `n = 160`, and the mean 3LIN value of a uniform
  right-hand side falls towards one half as the density grows.

This neither proves nor refutes UGC.
