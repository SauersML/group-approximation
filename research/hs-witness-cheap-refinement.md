---
rg: 2
id: hs-witness-cheap-refinement
kind: claim
title: A normalized HS witness refines its block at cost trace times square-root energy
---

Let `U_1,...,U_m` be unitaries in `M_d`, let `p!=0` be a projection, put
`a_s=pU_sp`, and normalize trace and Hilbert--Schmidt norm inside `pM_dp`.
For every self-adjoint `x in pM_dp` with

```text
tau_p(x)=0,
||x||_(2,p)=1,
E=sum_s ||a_sx-xa_s||_(2,p)^2,
```

there is a nonzero `q<=p` with `tau(q)<=tau(p)/2` such that, for `r=p-q`,
replacing the block `p` by the two blocks `q,r` increases the total ambient
boundary energy summed over all `m` generators by at most

```text
4 sqrt(2mE) tau(q).                                  (WCR)
```

This is the scale-sensitive form of the refinement estimate: a nearly
invariant witness is cheap in proportion to its actual Rayleigh energy, not a
preselected gap threshold.
