---
rg: 2
id: fpbs-worst-pair-rate-via-chemical-slope
kind: route
title: A conditional chemical slope below log gr over log(t/p_c) at the critical worst pairs gives a positive worst-pair rate above p_c
target: fpbs-worst-pair-connectivity-rate-positive-above-pc-universal
requires:
  - fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff
  - fpbs-worst-pair-chemical-slope-below-threshold-universal
---

**The two requirements.**

- **Established.** `fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff`,
  item 2: `gamma(t) >= log gr - l(t) log(t/p_c)` for every `t > p_c`.
- **OPEN.** Kernel (CS), `fpbs-worst-pair-chemical-slope-below-threshold-universal`:
  some `t > p_c` has `l(t) log(t/p_c) < log gr`.

**The step.** Together they give `gamma(t) > 0` at that `t`, which is exactly
the target (K).

**What each requirement can fail on.**

- The tradeoff is established, so it cannot fail.
- (CS) can fail while (K) holds: long detours on rare connections.

So this route replaces the analytic kernel (K) by a geometric statement about
chemical length. That statement comes with an explicit class of arguments that
cannot prove it; see the kernel.
