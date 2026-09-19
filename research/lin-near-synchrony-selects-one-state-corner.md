---
rg: 2
id: lin-near-synchrony-selects-one-state-corner
kind: claim
title: Near-synchrony rounding selects one state-dependent corner with relative row control
artifacts:
  - research/artifacts/lin-tracial-rounding-state-gh-source-audit-2026-08-23.md
  - research/artifacts/lin-state-local-cross-gram-exactification-2026-08-23.md
---

For a `delta`-synchronous tracially embeddable correlation with density
`sigma`, Lin's synchronous rounding supplies spectral corners `P_lambda` for
which

```text
integral tau(P_lambda) d lambda = tau(sigma^2)=1,
integral e_lambda d lambda <= O(delta^(1/4)+delta),
```

where `e_lambda` is the averaged squared row discrepancy on `P_lambda`.
Consequently some `lambda` with `tau(P_lambda)>0` satisfies

```text
e_lambda/tau(P_lambda) <= O(delta^(1/4)+delta).
```

This is a genuine common corner for one state.  It has no uniform trace
floor and is selected from `sigma`, rather than by a fixed group word.  It
therefore cannot by itself supply the common marked source in `(CPS2)` or
align corners arising from different context densities.

The failure remains true **relative to a macroscopic marked sector**, not
only relative to the ambient identity.  In `M_N` with normalized trace, let
`q<=p` have ranks `1` and `floor(N/2)`, respectively, and take
`sigma=sqrt(N)q`.  Then `tau(sigma^2)=1`, while positivity of Lin's layer
identity forces every nonzero spectral layer below `q`.  Hence

```text
tau(P_lambda)/tau(p) <= 1/(N tau(p)) -> 0.             (L4.2)
```

All state-seminorm estimates are concentrated on `q`, although the marked
projection `p` has asymptotic trace `1/2`.  Thus no constant `gamma>0` in a
bound `tau(P_lambda)>=gamma tau(p)` can be extracted from Theorem 4.1,
even when the density is supported inside the marked sector.  Equivalently,
declare the marked involution to be `J=I-2p`; then `p=(I-J)/2`, exactly the
normalization used in `(CPS2)`.

There is a sharp positive specialization. If the density is normalized from
one contraction `G` with `||G||_2^2>=m_0`, then its spectral mass is no
longer arbitrary relative to the relevant state.
`positive-cross-gram-state-rounds-to-common-pvm` selects a layer of trace at
least `m_0/2` and rounds both PVM packets on that layer. Thus this claim's
no-uniform-mass warning applies before a positive Gram certificate is given;
it is not an additional carrier-extraction gate after one is given.
