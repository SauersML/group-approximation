---
rg: 2
id: localized-loewner-pays-spike-or-boundary
kind: claim
title: Localized Loewner order pays every odd spike by anchor-row mass or boundary
distinct_from:
  adjoint-parity-cone-lifts-to-loewner-order: that proves a global superoperator max-fractional inequality; this tests it on a nonreducing physical spectral block and quantifies the boundary error.
  one-anchor-odd-spike-has-a-cheap-reducing-cut: that obtains a spectral cut from coarea; this shows why the resulting cut recovers the missing factor of code length once parity is used.
  central-adaptive-peeling-or-noncentral-stopping: that must select and sum many cuts; this proves the exact one-cut peeling-versus-boundary inequality.
---

ESTABLISHED.  Assume exact commuting parity faces for a code with
max-fractional pseudodistance `kappa L`.  Fix `a,i`, put
`R_(a,k)=Y_(a,k)^2`, and let

```text
 p=1_[s,1](R_(a,i)),
 D(p)=(1/L)sum_k ||[p,Q_k]||_2^2.                       (LLB1)
```

Then

```text
 s tau(p)
 <= (2/(kappa L))sum_k tau(pR_(a,k))
    +D(p)/(2kappa).                                     (LLB2)
```

Consequently either `D(p)>=kappa s tau(p)`, or

```text
 (1/L)sum_k tau(pR_(a,k))
 >=(kappa/4)s tau(p).                                   (LLB3)
```

There is no factor depending on `L`.

On `L_2(M)` take `P_k=(I-Ad(Q_k))/2`, `v=Q_ap`, and
`T_k=(Q_a-Q_kQ_aQ_k)p/2`.  Then

```text
 ||T_k||_2^2=tau(pR_(a,k)),
 ||P_kv-T_k||_2<=(1/2)||[p,Q_k]||_2.                    (LLB4)
```

For the selected site, `p` commutes with `Q_i`, so `P_iv=T_i`.  Apply
`P_i<=(kappa L)^(-1)sum_kP_k` to `v`, and use
`||P_kv||_2^2<=2||T_k||_2^2+(1/2)||[p,Q_k]||_2^2`.
Since `R_(a,i)>=sp` on `p`, this proves `(LLB2)`.

For a disjoint family of reducing cuts with the same anchor, the row terms
in `(LLB3)` sum to at most the original anchor-row energy.  Thus only the
boundary-heavy alternative remains to be summed globally.
