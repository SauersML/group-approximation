---
rg: 2
id: gap-and-floor-do-not-force-compatible-syndrome-effects
kind: claim
title: Constant combinatorial gap and a uniform energy floor do not force compatible local syndrome effects
artifacts:
  - research/artifacts/gap-floor-syndrome-separation-2026-09-16.md
  - experiments/gap-floor-syndrome-separation-2026-09-16/check_separation.py
invalidates:
  - compatible-syndrome-effects-from-gap-and-rounder-floor
distinct_from:
  amplifier-has-compatible-local-syndrome-effects: that asks for a construction on the NO outputs of the common amplifier, and positive shift trivializes its clauses; this refutes only the generic inference from gap, floor, rounder cost, locality and degree, on an explicit unshifted family that is not an amplifier output.
  qubit-pairs-have-half-gap-and-unbounded-rounder-cost: that family has vanishing energy floor and unbounded bare rounder cost; here the floor is at least 1/30 and the least bare rounder constant is at most 11, while compatible local effects still fail.
  nonorthogonal-pair-forbids-single-term-syndrome-ports: that excludes singleton neighborhoods for one pair; this excludes every neighborhood system of bounded occurrence, of any sizes, at every finite pair of constants, on a family with a uniform floor.
  fixed-term-chain-defeats-bounded-syndrome-neighborhoods: that uses fixed term matrices but has vanishing combinatorial gap and bounded neighborhood size; this has combinatorial gap at least 11/30 and allows unbounded neighborhood sizes, but its term matrices vary with N.
  amplifier-admits-a-uniform-local-kernel-resolution: that asks for kernel resolutions on the amplifier's NO outputs; this shows that such resolutions with uniform constants are not implied by gap, floor and bounded degree, as a corollary of the same test-vector count.
---

For integers `g>=3` and `N>=2` let `H(g,N)` be the following instance on qubits.
Take a graph `G` with at least one edge, maximum degree at most `512`, no cycle of length at most `g`,
and least monochromatic edge count at least `|E|/10`. Such a graph exists
by a self-contained probabilistic proof. Place the terms `|00><00|+|11><11|` on
the edges of `G`, and add `|E|` pair qubits carrying `P=|1><1|` and
`Q_N=ww^*`, where `w=(2N,N^2-1)^T/(N^2+1)`.

Every member has:

- locality two and norm-one projector terms;
- degree at most `512`;
- combinatorial gap at least `11/30`;
- normalized ground energy at least `1/30`;
- least bare rounder constant `s*/(m lambda_min)` at most `11`.

Let `C_0>=0` and `R>=1` be constants. Suppose `H(g,N)` admits isometries
`W`, commuting projections `B_a`, and neighborhoods `N(a)` of occurrence at
most `R`, with `W^*B_aW<=C_0 sum_(b in N(a)) h_b` for every term `a` and
`W^*Pi_S W=0` for every infeasible fault set `S`. Then `C_0>0` and
`min(g+1,(N^2+1)/(2C_0))<=3R`. Hence no such tuple exists when `g>=3R` and
`N^2+1>6C_0R`. Nothing is assumed about the size of `W` or of the
neighborhoods, or about physical realization.

The same bound holds for any POVM with these two properties. In particular,
kernel resolutions with occurrence `R` and spectral constant `delta` give it
with `C_0=1/delta`. A gadget-flag tuple with union map
`J -> union_(i in J) phi(i)` and `|phi(i)|<=M` gives
`min(g+1,(N^2+1)/(C_0R))<=3MR`.

The mechanism is a local frustration certificate. For every frustrated set `T`,
compatible effects force `I<=C_0 min(|T|,R) H_(union_(a in T) N(a))`.
Consequently, the union of the neighborhoods of a frustrated set must support
a uniformly gapped subsystem. In `H(g,N)` every such subsystem has more than
`g` edge terms or order `N^2` pair terms.

This is not a refutation of `amplifier-has-compatible-local-syndrome-effects`:

- positive shift satisfies its clauses trivially;
- the family is essentially classical: its energy problem lies in NP;
- the term matrices vary with `N`.

The version with a fixed finite collection of term matrices, a constant
gap and a uniform floor remains open. There, bounded frustrated sets are
automatically uniformly gapped, and this method gives nothing.
