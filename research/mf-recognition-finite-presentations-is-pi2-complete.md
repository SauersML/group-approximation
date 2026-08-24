---
rg: 2
id: mf-recognition-finite-presentations-is-pi2-complete
kind: claim
title: MF and non-MF recognition are second-level complete on finite presentation codes
root: true
distinct_from:
  mf-recognition-has-a-pi2-upper-bound: that proves the membership upper bound and properness over the first level; this asks for the missing FIN-hardness.
  mf-recognition-recursive-presentations-is-second-level-complete: that proves exact completeness before finite-presentation compilation.
---

The target classification is

```text
NONMF_fp is Sigma^0_2-complete,
MF_fp    is Pi^0_2-complete.
```

The upper bounds are established by
[[mf-recognition-has-a-pi2-upper-bound]].  The unresolved direction is

```text
FIN <=_m NONMF_fp.
```

This is deliberately open.  Neither Adian--Rabin nor generic effective Higman
embedding supplies the required eventual-stabilization switch with an MF
positive branch.

## Attempts

The recursive FIN switch is complete, but generic Higman embedding loses the
MF branch.  The recorded attack is the MF-safe compiler route below.
