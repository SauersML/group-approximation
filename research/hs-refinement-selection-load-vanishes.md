---
rg: 2
id: hs-refinement-selection-load-vanishes
kind: claim
title: Property T makes the total HS refinement selection load vanish with model defect
---

Fix a finitely generated property-`(T)` group `Gamma` and a finite symmetric
generating set `S`, with `m=|S|`.  There are a constant `kappa_0>0` and a
function

```text
omega(delta) -> 0  as delta -> 0
```

such that every normalized-HS `delta`-almost representation `phi` admits a
finite binary refinement tree starting at the block `1` with these rules.

- Every internal block `p` carries a self-adjoint normalized witness

  ```text
  tau_p(x_p)=0,
  ||x_p||_(2,p)=1,
  E_p=sum_(s in S) ||[p phi(s) p,x_p]||_(2,p)^2 < kappa_0^2.
  ```

- Its children are `q_p` and `p-q_p`, where `q_p` is a nonzero spectral cut
  supplied by weighted median coarea and

  ```text
  tau(q_p)<=tau(p)/2.
  ```

- Every leaf satisfies the scalar adjoint Poincare inequality with constant
  `kappa_0`.

The **selection load** of the tree obeys

```text
sum_(p internal) tau(q_p) sqrt(E_p) <= omega(delta).  (LOAD)
```

Finite dimension makes any such strict refinement process terminate once a
choice is made at every failed leaf; the content is the vanishing bound
`(LOAD)`.  It is exactly the global summability statement left after the
local spiky obstruction is removed by weighted coarea.

## Attempts

- Exact reducible representations are compatible with `(LOAD)`: cut along
  invariant projections, where `E_p=0`.
- The rank-one surgery obstruction is also compatible: its bad direction has
  vanishing trace and vanishing Rayleigh energy, so its contribution to the
  load tends to zero.  Thus the target is not contradicted by the known
  finite-window no-go.
- A proof must control a whole hierarchy at once.  Bounding only the number of
  cuts or only `sum tau(q_p)` loses a logarithm of the matrix dimension; the
  square-root energy factor is the quantity that can make the sum vanish.
- The next attack should search for a telescoping spectral potential whose
  drop under the median cut dominates `tau(q_p) sqrt(E_p)`.
