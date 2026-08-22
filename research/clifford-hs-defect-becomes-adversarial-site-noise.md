---
rg: 2
id: clifford-hs-defect-becomes-adversarial-site-noise
kind: claim
title: Convert growing Clifford-packet HS defect into bounded adversarial tensor-site weight
distinct_from:
  finite-schur-clifford-packet-flexible-hs-exactification: that exactifies one fixed finite packet with constants allowed to depend on it; this needs quantitative control uniform in a growing number of Clifford sites.
  robust-clifford-capacity-bound: that turns an already supplied approximate Clifford family into a dimension lower bound; this must first expose a repairable tensor-site error pattern suitable for a joint code.
---

Let an `n`-site Clifford/Pauli packet be addressed by words of length
`poly(log n)` inside a finite presentation, and let `Q` be a positive-density
approximately reducing carrier on which its defining relators have total
normalized-HS energy `E`.  Prove a dimension-free decomposition and repair
theorem of the following form.

There is a tensor realization

```text
Q H = (C^q)^(tensor n) tensor K
```

after discarding `o(tau(Q))` carrier mass, together with a set `B` of bad
tensor sites, such that the packet words outside `B` agree with exact site
Paulis and

```text
|B| <= F(n,E),
```

where `F(n,E)` lies below the adversarial correction radius of the joint code
from `bgv-adversarial-fault-tolerance` whenever `E=o(1)`.  The repair
must also control coherent errors, not only Pauli errors supplied in advance.

## Attempts

- Normalized HS norm is an average over Hilbert dimension, not Hamming weight
  over tensor factors.  A coherent perturbation can touch every prospective
  site while having small `2`-norm, so operator support cannot simply be
  declared to be a bad-site set.
- Gowers--Hatami exactification solves the fixed finite-group problem, but its
  constants and flexible-dimension loss are not presently controlled for the
  growing extraspecial groups needed here.
- Pauli twirling turns a channel into a Pauli distribution only after a stable
  tensor factorization exists.  Using twirling before proving that
  factorization is circular.
- `lin-code-space-pauli-test-has-only-logarithmic-weyl-rank` audits the most
  concrete proposed rigidity shortcut.  Lin's literal dimension-`log n`
  Justesen **code-space** sampler has a perfect strategy on only `O(log n)`
  qubits and a dense `C^perp` coherent gauge.  Replacing it by the generator
  columns of a dimension-`n`, length-`Theta(n)` code repairs global Pauli
  rigidity with logarithmic sampling, but only up to a global isometry; pinning
  that isometry to the named tape sites is still precisely the present claim.
