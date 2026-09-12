---
rg: 2
id: near-regular-finite-character-fixes-plancherel-types-proof
kind: route
title: Recover multiplicities by finite character orthogonality
target: near-regular-finite-character-fixes-plancherel-types
requires: []
---

Character orthogonality gives

```text
m_pi=(1/|H|)sum_(h in H) conjugate(chi_pi(h)) Tr(rho(h)).
```

Divide by `d`, isolate the identity term, and use `chi_pi(1)=d_pi`:

```text
m_pi/d-d_pi/|H|
 =(1/|H|)sum_(h!=1) conjugate(chi_pi(h)) t(h).
```

Since `|chi_pi(h)|<=d_pi`, `(NRC1)` implies

```text
|m_pi/d-d_pi/|H||<=d_pi(|H|-1)eta/|H|.
```

Multiplication by `d_pi` proves `(NRC2)`. For a fixed finite group, changing
the representation on an `epsilon` fraction of Hilbert dimension changes
every normalized isotypic mass and normalized trace by `O_H(epsilon)`, giving
the flexible-exactification addendum.
