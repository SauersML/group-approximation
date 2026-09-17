---
rg: 2
id: symbol-blind-automata-reduce-to-defect-counting
kind: claim
title: Symbol-blind automata are partition maps, and bijectivity at every alphabet is equivalent to finite defect-counting identities
distinct_from:
  certificate-controlled-routing-is-surjunctive: that routes data under a separate unchanged certificate; here the routing is read from the data's own equality pattern (self-controlled routing), which that node excludes.
  finite-injective-positive-charge-automata-are-surjective: that needs a unique zero symbol and a conserved positive charge on a finite alphabet; here there is no zero symbol and the conserved quantity (partition defect) lives on the space of set partitions of the group.
  bijective-ca-preserve-uniform-bernoulli-measure: that is the forward implication bijective => measure preserving for all automata; this node converts measure preservation of symbol-blind rules at all alphabet sizes into polynomial identities indexed by finite partitions, and proves the lowest orders over every group.
artifacts:
  - experiments/symbol-blind-automata-2026-09-17/partition_census.py
  - experiments/symbol-blind-automata-2026-09-17/census_results.txt
  - experiments/symbol-blind-automata-2026-09-17/census_order8.txt
---

Let G be any group and M a finite subset of G containing e. Call a cellular
automaton tau_q on [q]^G with memory M *symbol-blind* if it commutes with every
permutation of the alphabet [q].

**1. Normal form.** If q >= |M|+2, tau_q is a *selector*: there is a map sigma
from set partitions of M to M, choosing one class of each partition, with

    tau_q(x)(g) = x(g sigma(pi_g x)),

where pi_g x is the partition of M by m ~ m' iff x(gm) = x(gm'). The same
sigma defines tau_q for every q. Up to right multiplication by a fixed
element (a bijective automaton), sigma(discrete) = e.

**2. Partition criterion.** Write psi_P(g) = g sigma(pi_g P) for a set
partition P of G, and T(P) = psi_P^* P. Let Part_{<=q}(G) be the partitions
with at most q classes. Then:

- tau_q is injective iff T is injective on Part_{<=q}(G) and, for each such P,
  psi_P meets every class of P, except possibly one class when P has exactly
  q classes;
- tau_q is surjective iff T maps Part_{<=q}(G) onto itself.

Consequently injectivity passes from q to every q' <= q, and bijectivity at
infinitely many q gives bijectivity at every q (via 4).

**3. Sparse-defect transfer.** Suppose tau_q is injective for every q. Let
FD(G) be the partitions with finitely many non-singleton classes, all finite,
with defect sum (|C|-1). Then:

- T maps FD(G) injectively to itself;
- psi_P induces a bijection classes(T P) -> classes(P);
- T preserves the defect;
- T is bijective on defect-1 partitions (single pairs).

**4. Polynomial rigidity.** For finite F, E = FM, a partition pi of F and
j >= 0, define

    N_j^T(F,pi) = #{partitions P of E with defect j : T(P)|_F = pi}.

Here P is extended by singletons, and T(P)|_F depends only on P|_E. For a
pattern y in [q]^F with kernel pi (k classes),

    #{x in [q]^E : tau_q(x)|_F = y} = sum_j N_j^T(F,pi) (q-k)_{|E|-j-k}.

The following are equivalent:

- (a) tau_q preserves the uniform Bernoulli measure for infinitely many q;
- (b) tau_q preserves it for every q;
- (c) N_j^T(F,pi) = N_j^{id}(F,pi) for all F, pi, j.

Hence, among automata injective at every alphabet size: tau_q is bijective
for every q iff all identities (c) hold. The forward direction uses
bijective-ca-preserve-uniform-bernoulli-measure; the reverse uses closed
image plus full support.

**5. Lowest orders hold over every group.** If tau_q is injective for every
q, then N_0^T = N_0^{id} and N_1^T = N_1^{id} for all F and pi.

The open part is isolated in symbol-blind-defect-counting-identities
(orders j >= 2). No soficity, amenability or unimodularity is used anywhere
above.

Scope. The class contains self-controlled routings beyond translations. In
the census groups (Z/5, Z/6, S_3, Z/2 x Z/3, |M|=3) the nontrivial bijective
rules occur exactly when M is an order-3 subgroup, acting blockwise on
cosets. The census script decides bijectivity via criterion 2 on all set
partitions. On Z/7 with |M|=4 (three windows, 93312 rules each) only the
identity survives. On Z/8 and Z/2 x Z/4 with M = {0,1,4,5} (the product of an
order-2 subgroup with {0,1}), 31 nonidentity rules are bijective; with M =
{0,1,2,3} on Z/8 only the identity is. Over a finite group injectivity and
bijectivity coincide, so the census describes the class, not the conjecture.
