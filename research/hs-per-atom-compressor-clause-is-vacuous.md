---
rg: 2
id: hs-per-atom-compressor-clause-is-vacuous
kind: claim
title: An atom-by-atom compressor transport bound in normalized HS is automatic on small atoms
distinct_from:
  nonmonomial-multiplicity-obstructs-hs-compressor-transport: that shows compressor transport can genuinely fail for an exact representation of a Kazhdan pair; this shows that the atom-by-atom form of the transport clause is satisfied by the identity matching on every small atom, so it carries no size information at all.
  small-trace-rank-one-quarantine: that is a construction shattering an identified small region into rank-one atoms at linear boundary cost; this is a defect of a hypothesis, namely that a per-atom normalized-HS bound becomes automatic below trace eps^2/4.
  tracial-median-concentration: that asks for concentration of the block-size observable; this identifies which form of the compressor clause can supply the multiplicative size drift that concentration argument consumes.
---

**ESTABLISHED.**  Let `(p_j)` be pairwise orthogonal projections in `M_d`,
let `W` be a unitary, and fix `eps>0`.  Write `tau` for the normalized trace
and `||x||_2 = tau(x^*x)^(1/2)`.  Consider the atom-by-atom clause formerly
stated in `hs-expander-block-decomposition` and `leavitt-hs-block-compatibility`:
for every atom `p_j` there is an atom `p_(sigma(j))` with

```text
||W p_j W^* - p_(sigma(j))||_2 <= eps,
tau(p_(sigma(j))) >= tau(p_j) - eps.                                (PA)
```

1. Every atom with `tau(p_j) <= eps^2/4` satisfies `(PA)` with `sigma(j)=j`,
   whatever `W` is.
2. More generally, `(PA)` holds for **any** choice of `sigma(j)` among the
   atoms of trace at most `eps^2/4`, whenever `tau(p_j) <= eps^2/4`.  So on
   small atoms `(PA)` permits every size ratio `tau(p_(sigma(j)))/tau(p_j)`.

Consequently `(PA)` does not imply the multiplicative size drift used by the
median step of the one-sided-compression argument,

```text
M(sigma(j)) >= (1-eta) M(j)  outside atoms of total trace o(1),      (6)
```

in any regime where atom traces are below `eps(delta)^2/4` on order-one mass.
That is the generic regime: irreducible summands of regular-type
representations have vanishing trace.

The repaired, mass-weighted clause

```text
sum_j ||W p_j W^* - p_(sigma(j))||_2^2 <= eps                        (MW)
```

does imply `(6)`: outside atoms of total trace at most `8 eps + sqrt(eps)`,
`sigma` is injective and `tau(p_(sigma(j))) >= (1 - 2 eps^(1/4)) tau(p_j)`.
`(MW)` is the literal tracial form of estimate `(5)` of
`official/counterexample.tex`, which bounds total unmatched vertex mass rather
than each component separately.  The consumer nodes now state `(MW)`.

Derivation: `hs-per-atom-compressor-clause-is-vacuous-proof`.
