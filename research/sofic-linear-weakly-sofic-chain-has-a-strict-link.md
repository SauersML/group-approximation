---
rg: 2
id: sofic-linear-weakly-sofic-chain-has-a-strict-link
kind: claim
title: For every field, sofic is strictly smaller than linear sofic or linear sofic is strictly smaller than weakly sofic
distinct_from:
  weakly-sofic-not-sofic: that is the separation of the two ends of the chain; this locates it inside the chain for every field and names the two exclusive-or payoffs.
  linear-sofic-nonsofic-group: that asks for the lower strict inclusion specifically; this proves that one of the two inclusions is strict without deciding which.
---

ESTABLISHED.  Fix any field `F`.  At least one of

```text
sofic  <  F-linear sofic        F-linear sofic  <  weakly sofic
```

is a strict inclusion of classes of countable groups.

The two inclusions hold by [[sofic-implies-linear-sofic-over-every-field]] and
[[linear-sofic-implies-weakly-sofic-over-every-field]].  If both were
equalities, weakly sofic would equal sofic, contradicting
[[weakly-sofic-not-sofic]].

The Kun--Thom wreath `W` already witnesses the separation.  Whichever
inclusion is strict, `W` decides it: `W` is weakly sofic and nonsofic, so
either `W` is `F`-linear sofic, and the lower inclusion is strict, or it is
not, and the upper one is.  See [[kun-thom-wreath-linear-sofic]] and
[[kun-thom-wreath-not-linear-sofic]].
