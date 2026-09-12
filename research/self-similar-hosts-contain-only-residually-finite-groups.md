---
rg: 2
id: self-similar-hosts-contain-only-residually-finite-groups
kind: claim
title: Subgroups of self-similar groups are residually finite, so Thompson's V embeds in no self-similar group
invalidates:
  - boone-higman-via-universal-fp-self-similar-host
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that is the imported payoff theorem for finitely presented self-similar groups; this is the scope obstruction showing that such hosts can only contain residually finite inputs.
  every-fp-rf-group-embeds-in-fp-self-similar-group: that is the open embedding claim for finitely presented residually finite inputs; this proves that restricting to residually finite inputs is forced, and excludes every infinite simple input.
---

**ESTABLISHED.** Every subgroup of a self-similar group `H <= Aut(T_d)` is
residually finite. In particular no infinite simple group embeds in a
self-similar group. Thompson's group V is finitely presented, infinite and
simple, and has solvable word problem. So V is a finitely generated group with
solvable word problem that embeds in no self-similar group.

## Consequences

- `every-decidable-group-embeds-in-fp-self-similar-group` is false.
- The route `boone-higman-via-universal-fp-self-similar-host` is dead.
- By `boone-higman-iff-infinite-simple-inputs`, the conjecture is equivalent to
  its restriction to infinite computably presented simple inputs. None of those
  is residually finite, so self-similar hosts reach none of the inputs that
  carry the general conjecture. The self-similar method only serves
  `fp-residually-finite-boone-higman`, through
  `fp-rf-boone-higman-via-fp-self-similar-overgroups`.
- For the general conjecture, self-similar machinery must enter through hosts
  acting on Cantor space that contain non-residually-finite groups, such as
  Rover--Nekrashevych commutator subgroups:
  `decidable-groups-embed-in-rover-nekrashevych-hosts`.
