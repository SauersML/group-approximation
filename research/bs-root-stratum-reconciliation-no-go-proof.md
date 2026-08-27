---
rg: 2
id: bs-root-stratum-reconciliation-no-go-proof
kind: route
title: Apply irreducible uniqueness to the adjacent fourth-power clocks
target: bs-root-strata-have-no-energy-paid-invariant-reconciliation
requires:
  - long-bs14-packets-defeat-invariant-op-thresholding
  - iwahori-cycle-packet-determinant-fence
---

The required claim supplies the explicit matrices `(R_m,S_m,T_m)`, proves
their exact covariance and the estimate `(BSR2)`, and proves that the two
cores are distinct irreducible BS representation types.  Unique
decomposition of finite-dimensional unitary representations implies
`(BSR3)`: if the enlargements were equivalent, the `c_m` type would have to
occur in `pi`, already forcing `dim(pi)>=m` (and symmetrically for `tau`).
The relative-rank and limiting contradiction then follow exactly as stated.

For even `m`, the geometric sum gives
`det(S_m)=exp(2 pi i/3)`, while `det(T_m)=det(S_m)^2` and the cyclic shift
has determinant `-1`.  Substitution into `(PDF3)` of the second required
claim gives `-1` in both cases, proving the nonextension firewall.
