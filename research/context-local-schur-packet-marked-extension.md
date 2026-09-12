---
rg: 2
id: context-local-schur-packet-marked-extension
kind: claim
title: Context-local Schur packets extend every marked BCS representation after infinite amplification
distinct_from:
  toeplitz-schur-bcs-shift-amalgam: that must additionally impose the cross-level Toeplitz return incidences; this proves exact completeness before those incidences are added.
  finite-selector-gadget-induction-barrier: that says every selector character survives a finite overgroup; this explicitly retains every character and supplies its rank-dependent packet module.
---

Let `pi` be a unitary representation of a finite BCS word system on a Hilbert
space `H`, and let `w` be a BCS word with `pi(w)!=I`. For every context `c`,
choose a Boolean predicate `f_c` on its commuting involutions and its finite
Schur--Clifford packet `A_c<=B_c`.

After replacing `H` by one infinite amplification `H tensor K`, all the
context packet generators can be represented simultaneously so that:

1. their input selector generators are the corresponding amplified BCS
   involutions;
2. the common packet sign is `-I`;
3. every defining relation of every `B_c` holds exactly; and
4. `w` remains nonidentity.

No commutation between packet generators belonging to different contexts is
asserted. Thus this theorem preserves contextuality and passes the classical-
CSP falsification test. It supplies the local exact-model extension needed by
a Schur compiler; any remaining completeness obstruction comes from the
global return/transport relations.
