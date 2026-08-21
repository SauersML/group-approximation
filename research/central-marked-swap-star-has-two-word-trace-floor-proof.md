---
rg: 2
id: central-marked-swap-star-has-two-word-trace-floor-proof
kind: route
title: Apply the binary star trace formula in the marked corner and Fourier-isolate it by h minus yh
target: central-marked-swap-star-has-two-word-trace-floor
requires:
  - even-partial-swap-star-has-canonical-trace-floor
---

Normalize the trace on the nonzero corner `pH`.  The binary case of
`even-partial-swap-star-has-canonical-trace-floor` gives

```text
Re tau_p(h)>=1/4.
```

Multiplying by `tau(p)` proves `(MSS3)`.  Since `p=(1-y)/2` and `y` is
central,

```text
tau(h)-tau(yh)=tau((1-y)h)=2 tau(ph).
```

This proves `(MSS4)`.  Two-factor word telescoping proves `(MSS6)`.  In an
exact star with nonzero source, `h` acts nontrivially as a three-cycle on the
source and two range copies; on the same subspace `yh=-h`, so neither word
is identity.  Canonical trace separation then gives `(MSS5)` and the stated
nonhyperlinearity criterion.

For the extension, multiply
`tau(p_chi h)>=tau(p_chi)/4-o(1)` by `|C|` and expand `(MSS7)`.  This is
exactly `(MSS8)`.  Canonical trace kills every nonidentity `c` and every
nonidentity `ch`, giving the asserted limits.
