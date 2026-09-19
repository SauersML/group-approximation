---
rg: 2
id: amenability-fp-position-proof
kind: route
title: Kesten upper bound plus the classical Adian--Rabin reduction with the trivial witness and F_2 forbidden
target: amenability-of-finite-presentations-arithmetical-position
requires:
  - amenability-two-generator-recursive-is-pi2-complete
---

Membership: the `Pi^0_2` form (AM2) is proved in
[[amenability-two-generator-recursive-is-pi2-complete]] for every finitely
generated recursive presentation, in particular for finite ones.

Hardness: in the Adian--Rabin construction (Lyndon--Schupp IV.4.1;
Miller's survey), for a Markov property with positive witness `A` and
forbidden group `E`, the computable family `w |-> L_w` built from a
finitely presented group with unsolvable word problem satisfies `L_w ~= A`
when `w = 1` and `E <= L_w` when `w != 1`.  Take `A = 1` and `E = F_2`:
amenability passes to subgroups and `F_2` is not amenable, so `L_w` is
amenable iff `w = 1`.  The word problem is `Sigma^0_1`-complete.
