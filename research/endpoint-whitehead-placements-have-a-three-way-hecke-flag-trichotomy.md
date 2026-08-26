---
rg: 2
id: endpoint-whitehead-placements-have-a-three-way-hecke-flag-trichotomy
kind: claim
title: Every endpoint Whitehead placement either dresses, ejects the quarter flag, or halves the eighth flag
artifacts:
  - research/endpoint-whitehead-placement-trichotomy-proof.md
  - experiments/endpoint_chain_center_hecke_collision_audit.py
distinct_from:
  endpoint-whiteheads-are-center-chain-hecke-spectators: that treats the all-spare endpoint placement and obtains a spectator-compressed one-eighth Gram; this classifies every legal coordinate placement and isolates the unique fine-only collision type.
  endpoint-detector-cell-retains-coboundary-gauge: that transports the full detector cell through an arbitrary fresh endpoint chain; this asks how every such chain meets the literal center-chain quarter/eighth flag packet.
  native-whitehead-corner-collapses-hecke-flags: that computes the largest common reducing corner for the two original native Whiteheads; this treats fresh endpoint Whiteheads and shows that the only proper fine compression is a fixed regular half of the eighth flag.
---

**ESTABLISHED COMPLETE PLACEMENT FENCE.**  Retain the center-chain signed
groups

```text
H=<C_1,C_2,C_3>,
K_1=<H,v,w>,                    K_2=<H,v,w,s>,
v=x_57(a_1),  w=x_67(a_1),     s=x_68(a_2),            (EPT1)
```

of orders `64,256,512`, with character `-1` on the three simple
`q`-roots and `+1` on `v,w,s`.  Their character projections are

```text
e=e_(H,chi),        p_1=e_(K_1,lambda),
p_2=e_(K_2,lambda)<=p_1.                                (EPT2)
```

Consider any legally oriented adjacent endpoint Whitehead carrying

```text
x_(1,r)(a_m),x_(r,3)(b_m)
  to x_(1,r')(a_(m+1)),x_(r',3)(b_(m+1)),              (EPT3)
```

where `r,r'` are distinct and avoid the marked coordinates `1,3`.
Every orientation and every coordinate placement falls into exactly one of
the following types.

1. If neither endpoint is `7` or `8`, the Whitehead preserves the signed
   groups `H,K_1,K_2`.  On the flag projections it is a full reducing
   unitary, so its use in a Hecke cross Gram is only a reservoir dressing.
2. If an endpoint is `7`, the Whitehead fails to normalize `K_1` and
   therefore ejects the quarter flag.  It cannot define a fixed-source map
   on either prescribed unequal row.
3. If an endpoint is `8` but neither endpoint is `7`, the Whitehead
   preserves `H,K_1` but fails to normalize `K_2`.  This is the only
   noncentral collision which distinguishes the two flags.

Coordinates outside `{2,4,5,6,7,8}` are all one generic spare type in this
classification.  The exact MSI enumeration checks both orders of every
pair in `{2,4,5,6,7,8,9}`, where `9` represents that spare type, at both
prefix depths.  Thus it covers every placement in rank `20`; the remaining
coordinates have no additional incidence with `(EPT1)`.

The promising chain `(r_1,r_2,r_3)=(7,8,2)` realizes the third type on its
second edge.  If `W=What_(8,2;2)`, then

```text
WvW=v,              WwW=w,
WsW=s':=x_62(a_3),
WA_1W=A_1,          WA_2W=x_52(a_3).                  (EPT4)
```

Moreover, for `K_2'=WK_2W`,

```text
|K_2'|=512,      K_2 intersect K_2'=K_1,
|<K_2,K_2'>|=1024,                                        (EPT5)
```

and the two signed characters extend to their join.  Hence, writing

```text
p_*:=e_(<K_2,K_2'>,lambda),
```

one has

```text
p_2(Wp_2W)=p_*,                 tau(p_*)=tau(e)/16,
(p_2Wp_2)^*(p_2Wp_2)=p_*.                             (EPT6)
```

Thus the noncentral placement gives a genuine proper fixed-source
compression: it keeps the whole quarter flag but retains exactly half of
the eighth flag.

This still is not an odd raw-row occurrence.  The projection `p_*` is a
fixed positive group-algebra character projection, exists with the same
mass in the canonical regular trace, and is reduced by `W`, which swaps
`K_2` and `K_2'`.  On `p_*` the moved and original fine flags have become
the same identity support.  The displayed noncentral information is the
even conjugation row `WsW=s'` (and likewise for `A_2`); it does not conjugate
either native source reflection to its controlled Hecke target.  Promoting
this fixed cut to the two affine selector rows would hit the regular-trace
firewall immediately.

Consequently no endpoint-chain coordinate choice closes the native
occurrence seam.  The only choice that distinguishes `p_1` from `p_2`
produces a fixed regular half-cut and collapses the distinction on its
reducing core.  A successful continuation must add a different ordinary
word with odd individual-row parity and a representation-dependent
relation-paid kernel; changing endpoint coordinates or orientation cannot
supply it.

No Property `(T)`, canonical microstate assumption, literature theorem,
local computation, or Lean compilation is used.

DERIVATION
endpoint-whitehead-placement-trichotomy-proof
