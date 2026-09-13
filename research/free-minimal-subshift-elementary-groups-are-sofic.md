---
rg: 2
id: free-minimal-subshift-elementary-groups-are-sofic
kind: claim
title: Elementary groups over crossed products of free minimal Z^2 subshifts of finite type are sofic modulo centre
distinct_from:
  free-minimal-subshift-elementary-groups-are-simple-kazhdan: that proves simplicity, (T) and linear soficity; this asks for soficity, which a counterexample would separate from linear soficity.
  linear-sofic-nonsofic-group: that is Arzhantseva--Paunescu Question 8.5 in general; this is one concrete family where a negative answer to it would live, and where a positive answer would feed the ring route.
---

**OPEN.** For every free minimal `Z^2`-SFT `Ω`, prime power `q` and `n >= 3`, the group
`S_n = EL_n(LC(Ω, F_q) ⋊ Z^2) / Z` is sofic.

The statement covers every rank on purpose. Soficity passes to subgroups but not to overgroups, so
the case `n = 3` would not reach the rank `n >= 4` that gate (b) fixes.

**Win-win.**
- **If true.** With `free-minimal-z2-sft-is-quantum-rigid` and `rigid-sft-elementary-group-mod-centre-is-fp`,
  it gives `sofic-fp-simple-kazhdan-group-from-fp-simple-ring`.
- **If false at some `Ω`.** `S` is `F_q`-linear sofic (`free-minimal-subshift-elementary-groups-are-simple-kazhdan`)
  and not sofic. That answers `linear-sofic-nonsofic-group` over a finite field, with a simple
  Kazhdan witness.

## Attempts

- **The periodic-model LEF mechanism: unavailable.** For `d = 1` the group is LEF. For SFTs without
  finite orbits the ring has no periodic models (peer Theorem A in
  `research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md`).
  - If `R_Ω` and `S` are finitely presented, `S` is not LEF, since it is infinite and simple.
  - LEF of `S` from some other finite model is not excluded when `R_Ω` is not finitely presented.
- **Rank to Hamming: blocked.**
  - The Følner models give only rank models.
  - The graph's bridge `monomial-rank-models-are-hamming-models` needs models within `o(N)` rank of
    monomial matrices. Root elements `1 + f u^g E_ij` truncate to unipotent non-monomial matrices,
    and every natural finite `GL_N(F_q)`-set turns a rank defect `r` into a Hamming defect
    `1 - q^(-O(r))`.
- **Weak soficity: reduces to an open claim.** `S` is weakly sofic
  (`linear-sofic-implies-weakly-sofic-over-every-field`). So `fg-simple-weakly-sofic-groups-are-sofic`
  would settle this claim.
- **Certificates excluded in the finitely presented case.**
  - No realization in an amenable orbit full group (`kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`).
  - No sofic embedding with ergodic centralizer (`kazhdan-ergodic-sofic-centralizer-forces-lef`).
  - No permanence construction, by (T) and simplicity.
- **Measure-theoretic action.** `S` acts on `Ω × (F_q^3)^(Z^2)` by fibrewise linear cellular
  automata commuting with the diagonal shift. It preserves the product of the invariant measure and
  Haar measure, and the action is essentially free. So soficity of `S` would follow from soficity of
  its orbit equivalence relation. That relation is not amenable, because of (T), and no argument is
  recorded.
