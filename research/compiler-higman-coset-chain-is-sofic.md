---
rg: 2
id: compiler-higman-coset-chain-is-sofic
kind: claim
title: The positive compiler Higman hosts have sofic coset models along the separating bridge chain
distinct_from:
  higman-host-coset-soficity-makes-compiler-rope-sofic: That proves a conditional implication from these coset models; this asks that the actual positive-branch hosts satisfy its hypothesis.
  first-rope-edge-coset-action-is-sofic: That concerns the larger first-rope action; this is a sufficient condition involving only the Higman host and its embedded bridge.
  mf-compiler-positive-branch-is-hyperlinear: That is the weaker unitary approximation endpoint; these permutation coset models would prove it but are not asserted necessary.
artifacts:
  - research/artifacts/liu-new-frontiers-2026-09-20.md
---

For every finite presentation code d and every e in INF, use the
construction of [[mf-compiler-is-uniform-in-finite-seeds]], seeded by
Carrier(d). Write iota:Q_e(d) -> H_e(d) for its Higman embedding and
j:Q_e(d) -> P=F_2 x F_2 for the positive bridge embedding. There exists
a descending separating chain of finite quotients r_n of P such that,
putting J_n=j^-1(ker r_n), the action H_e(d) on H_e(d)/iota(J_n) is
sofic in the GKP set-action sense for every n.

This is an OPEN sufficient route, not a consequence of hyperlinearity or
soficity of Q_e. It demands compatible coset information in the actual
Higman host. It quantifies over every seed and every positive index;
it is not enough to produce one convenient presentation of the abstract
bridge. The chain may depend on d,e; no effective selection of the
chain or its sofic models is required by this qualitative condition.

## Attempts

2026-09-20: the existing host-coset reduction supplies the exact chain
needed, so full permanence for every subgroup is unnecessary. A first
test is to track iota(J_n) through the explicit Higman HNN steps and
check whether the finite coset colors can be retained at each step.
Ordinary Higman embedding guarantees neither this action approximation
nor even soficity of the host. Replacing H_e by the known RF overgroup P
on INF is not a uniform compiler: detecting INF would be required.
MF models alone cannot supply this implication after the Liu-based
MF/nonhyperlinear separation. The unitary positive branch may still
succeed without this stronger permutation hypothesis.
