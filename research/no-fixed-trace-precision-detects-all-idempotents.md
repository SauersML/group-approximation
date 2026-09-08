---
rg: 2
id: no-fixed-trace-precision-detects-all-idempotents
kind: claim
title: Nonzero scalar idempotents in finite cyclic groups can evade any fixed lifted-trace precision
distinct_from:
  finite-precision-lifted-trace-obstruction: that provides a sufficient precision depending on subgroup order and matrix size; this proves that a uniform constant precision fails even in scalar finite cyclic group algebras.
  leavitt-trace-balanced-nested-idempotents: that balances characteristic-two cocenter traces for one pair; this gives nonzero idempotents with arbitrarily high valuation of the lifted identity trace.
artifacts:
  - research/artifacts/kaplansky-finite-precision-trace-2026-09-07.md
---

For each prime p and r>=1, put m=p^r+1 and H=C_m. The nonzero idempotent

    e = 1 - m^(-1) sum_(g in H) [g] in F_p[H]

has lifted trace p^r/(p^r+1). Thus t_(p,k)([e])=0 for k<=r and is
nonzero for k=r+1. The bound in
`finite-precision-lifted-trace-obstruction` is attained by this family.

No fixed prime-power precision detects all nonzero scalar idempotents,
even over finite cyclic groups. These idempotents are not actual inverse
defects: the higher nonzero trace excludes that possibility in every
ambient group containing H. This result identifies a limit of any proof
shortcut that replaces the full lifted invariant by one fixed modulus.
