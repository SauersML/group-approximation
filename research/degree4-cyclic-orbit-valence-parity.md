---
rg: 2
id: degree4-cyclic-orbit-valence-parity
kind: claim
title: Equal degree-four residual valence fixes the cyclic word length
artifacts:
  - research/artifacts/classify-degree4-strict-four-cycle.py
---

For a cyclic word with stable-letter exponents in `{+1,-1}` and total
exponent four, retain a distinct formal coefficient in every slot.  If the
four Reidemeister--Schreier orbit valences are `v_0,...,v_3`, then

```text
v_0+v_1+v_2+v_3 = n,       and every v_i is odd,
```

where `n` is the number of coefficient/stable-letter slots.  In particular,
an orbit profile `(1,1,v,v)` forces `v` odd and `n=2v+2`.  Thus the strict
three-corner four-cycle is necessarily length eight, the five-corner search
is necessarily length twelve, and the next equal-residual topology is
length sixteen with seven corners.

