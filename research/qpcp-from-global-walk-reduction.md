---
rg: 2
id: qpcp-from-global-walk-reduction
kind: route
title: Iterate global tensor amplification with a reducer whose loss is below its linear gain
target: quantum-pcp-constant-gap-local-hamiltonian
requires:
  - global-walk-linearly-amplifies-hamiltonian-energy
  - global-walk-reducer-has-net-energy-gain
  - bmvz-iterable-tensor-gap-amplification
artifacts:
  - research/artifacts/qpcp-strengthened-amplification-2026-09-20.md
  - research/artifacts/qpcp-strengthened-amplification-replay-2026-09-20.json
  - research/artifacts/qpcp-global-walk-amplification-2026-09-11.md
---

Use only the exponentially complete 5-local hardness seed and explicit
expander input from the BMVZ prerequisite; the global amplifier is the
separately proved positive-sandwich theorem. Put `B_t=(t+1)/2` and
`theta=L/B_t<1`. For each NO instance one full round satisfies

```text
epsilon_(i+1) >= B_t epsilon_i/[L(1+B_t epsilon_i)],
z_(i+1) <= theta z_i+L,  where z_i=1/epsilon_i,
epsilon_r >= 1/[theta^r/epsilon_0+L(1-theta^r)/(1-theta)].
```

Starting at `epsilon_0>=1/q(N)`, choose `r=O(log N)` with
`theta^r q(N)<=1`. The NO energy is then at least the fixed positive
`g=1/[1+L/(1-theta)]`. For YES instances pad the seed to `n_0>=N`;
site count never decreases. With `K=max{1,At}` and `a_0<=2^(-N)`,

```text
a_r <= K^r(a_0+r 2^(-N)) <= K^r(r+1)2^(-N),
```

which is eventually below `g/4`. The finitely many smaller input lengths
can be handled separately. Fixed rational bounds above `theta` and below
`g` suffice; no oracle for fixed real constants is needed.

The reducer's bounds on sites, terms and maximum term-description bit
length give a fixed linear resource recurrence, hence polynomial size
through logarithmically many rounds. Each call and the entire algorithm
run in polynomial time. Locality stays `k_0` and local dimension two.
Section 3 of the September 20 artifact proves every step, including the
exact reciprocal iteration and the `t=10,L=5` regression.

This conditional route is valid for every integer `t>=2`. It constructs
no reducer. The root remains open on the reducer prerequisite.
