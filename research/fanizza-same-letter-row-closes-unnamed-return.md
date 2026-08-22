---
rg: 2
id: fanizza-same-letter-row-closes-unnamed-return
kind: route
title: Turn the one Fanizza HNN row into an unnamed square-return carrier
target: unnamed-fixed-space-wandering-promotion
requires:
  - fanizza-same-letter-compressed-row
  - hnn-compressed-row-is-unnamed-fixed-carrier
---

Use the projection `P_U=t(U)p_Ut(U)^*` and the Britton word
`w=a t a^(-1)t^(-1)`.  The established HNN identity gives

```text
tr(P_U)>=alpha-o(1),
||(w(U)-1)P_U||_2=o(1),
```

and therefore the required square-return estimate with at most twice the
error.  Britton's lemma supplies the infinite-order normal form.

