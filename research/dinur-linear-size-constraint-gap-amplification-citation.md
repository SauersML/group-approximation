---
rg: 2
id: dinur-linear-size-constraint-gap-amplification-citation
kind: route
title: Import Dinur's preprocess-power-compose amplification theorem
target: dinur-linear-size-constraint-gap-amplification
requires: []
---

Citation import from Irit Dinur, *The PCP theorem by gap amplification*, JACM
54(3), 2007. The exact package used here is Theorem 1.5:

```text
UNSAT(G') >= min(2 UNSAT(G),alpha),       size(G')<=C size(G),
```

with perfect completeness. Its proof combines the preprocessing lemma, the
expander graph-powering amplification lemma, and alphabet reduction by an
assignment tester. No quantum or group-valued conclusion is imported.

