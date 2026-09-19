---
rg: 2
id: corona-hs-radical-is-finite-residual
kind: claim
title: Corona trace-invisibility in the commuting-lamp quotient is exactly the finite residual
distinct_from:
  kazhdan-asymptotic-commutant-transport: That is the general one-element transport theorem; this claim iterates it over all telescope levels and computes the resulting invisible set exactly for `W/<zeta>`.
  corona-corner-detection-criterion: That criterion makes the normal closure of the defect corner-invisible in any ambient group; this claim identifies the invisible set with the finite residual, which is strictly larger than that normal closure here.
  universal-mf-quotient: That claim is the general functorial statement that the MF radical produces a largest MF quotient; this one computes a different radical, the corona trace-invisible set, for one concrete group.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

For every corona representation `Theta` of `W/<zeta>`, the induced tracial
representation into the tracial ultraproduct kills the whole level-even lamp
subgroup `L_0`; and every element outside `L_0` is detected in normalized
Hilbert--Schmidt norm by some corona representation.  So

```text
{ g : Theta_2(g) = 1 for every corona representation Theta }  =  L_0
                                                              =  finite residual.
```

Consequently `Rad_MF(W/<zeta>)` is a `V`-submodule of `L_0`, and any corona
representation detecting an element of `L_0` must send it to a symmetry
`1 - 2p` with `p` a nonzero projection of vanishing normalized rank.
