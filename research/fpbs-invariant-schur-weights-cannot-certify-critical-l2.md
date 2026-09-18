---
rg: 2
id: fpbs-invariant-schur-weights-cannot-certify-critical-l2
kind: claim
title: Critical Schur weights form a compact space with no invariant measure, so no invariantly random or coamenably fixed weight certifies the critical L2 bound
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is the open conjecture that ||T_(p_c)|| is finite; this proves nothing about finiteness and instead restates it as nonemptiness of a compact Gamma-space of Schur weights, and shows that space never carries an invariant probability measure.
  fpbs-free-product-cayley-graphs-have-critical-l2-gap: that exhibits one Schur weight (a Busemann weight on the block tree) for free products; this explains why any such weight must be boundary-type, since its stabilizer cannot be coamenable.
  fpbs-hyperbolic-nonunimodular-critical-l2-gap: that imports strict gaps for hyperbolic and nonunimodular graphs; this is a method obstruction valid on every Cayley graph, amenable or not.
  fpbs-soft-collapse-iff-invariant-sparse-spines: that kills axiom sets satisfied by invariant non-Bernoulli families; this keeps the true Bernoulli kernel and kills the class of invariantly produced Schur certificates for it.
artifacts:
  - experiments/invariant-schur-weight-obstruction-2026-09-17/tree_schur_ratios.py
  - experiments/invariant-schur-weight-obstruction-2026-09-17/tree_schur_ratios.out
---

**ESTABLISHED (class-killing obstruction).** Proof in
`fpbs-invariant-schur-weights-transport-proof`.

Let `Gamma` be a finitely generated group, `S` a finite symmetric generating
set, `G = Cay(Gamma,S)` with root `o = e`, `0 < p < 1`, and
`tau_p(u,v) = P_p(u <-> v)`, `T_p` the matrix `tau_p`,
`chi_p = sum_v tau_p(o,v)`. For `C > 0` let

```text
W_C(p) = { h : Gamma -> (0,infinity) :  h(o) = 1,  (T_p h)(v) <= C h(v) for all v },
(g.h)(v) = h(g^(-1) v) / h(g^(-1) o).
```

1. **Compact certificate space.** `W_C(p)` is a compact metrizable space in the
   product topology, `Gamma` acts on it continuously, and
   `||T_p||_(2->2) = inf { C : W_C(p) is nonempty }`.
2. **Transport bound.** If `W_C(p)` carries a `Gamma`-invariant Borel
   probability measure, then `chi_p <= C`. So a Schur certificate drawn
   from any invariant probability law is never better than the constant weight,
   whose ratio is `chi_p`.
3. **Critical form.** At `p = p_c(G)`, for every `C`, the compact
   `Gamma`-space `W_C(p_c)` carries no invariant probability measure. For every
   `h` in `W_C(p_c)`, the stabilizer `Stab_Gamma(h)` is **not coamenable** in
   `Gamma`. In particular it contains no normal subgroup `N` with `Gamma/N`
   amenable.
4. **Calibration (amenable case).** If `Gamma` is amenable, every nonempty
   `W_C(p)` has an invariant measure, so items 1 and 2 give
   `||T_p||_(2->2) = chi_p`. At `p_c` this is infinite. This is the known
   amenable statement, recovered from the obstruction.

**What it kills.** Every method that certifies `||T_(p_c)|| < infinity` by a
Schur test whose weight is produced from `Gamma`-invariant randomness, or is
projectively invariant under a coamenable subgroup, fails at the mass-transport
step. This includes:

- constant and quasi-constant weights;
- weights that are factors of iid labels or of any invariant percolation,
  spanning forest or random end;
- averages of weights over an invariant probability law;
- weights depending only on the coordinate in an amenable quotient `Gamma/N`,
  for example exponential tilts along a `Z` factor.

The invariant is the transport balance
`sum_v tau(o,v) E[h(v)/h(o)] = sum_v tau(o,v) E[h(o)/h(v)]`, combined with
`r + 1/r >= 2`.

**The gate.** A certificate must be boundary-type: its orbit closure in
`W_C(p_c)` is a compact `Gamma`-space with no invariant measure. The known
cases fit this.

- The free-product weight `theta^(b/2)` is fixed by the stabilizer of an end of
  the block tree.
- Hutchcroft's `Delta^(1/2)` weight is fixed by a transitive nonunimodular
  closed subgroup of `Aut(G)`. There the mass-transport step itself fails, and
  this is exactly the hypothesis item 2 uses.

The script `experiments/invariant-schur-weight-obstruction-2026-09-17/tree_schur_ratios.py`
checks this on `T_3 = Cay(Z/2*Z/2*Z/2)` at `p_c = 1/2`:

- the constant weight has Schur ratio `1 + 3J/2`, which diverges;
- the Busemann weight `2^(-b/2)` has bounded ratio `8.7426...`;
- the radial weight `(1+|v|)2^(-|v|/2)` has ratio `16.985...` on levels up to 60.

**Remark (not load-bearing).** The same proof works when `G` is
transitive and `Gamma` is replaced by a closed transitive unimodular subgroup
of `Aut(G)`, using the unimodular mass-transport principle of
Benjamini–Lyons–Peres–Schramm (GAFA 1999). It fails when that subgroup is
nonunimodular, which is where Hutchcroft's theorem lives.
