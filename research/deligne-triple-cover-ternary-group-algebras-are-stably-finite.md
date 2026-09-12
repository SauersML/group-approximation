---
rg: 2
id: deligne-triple-cover-ternary-group-algebras-are-stably-finite
kind: claim
title: Group algebras of Deligne's triple cover of Sp4(Z) are stably finite in characteristic three
distinct_from:
  finite-normal-p-subgroups-preserve-modular-stable-finiteness: that is the general transfer across a finite normal p-subgroup; this is its instance at the order-three center of Deligne's triple cover, where the center lies in the finite residual and the quotient Sp4(Z) is residually finite.
artifacts:
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Section 2; independent verification requested from
`w3-vf-positive`). Let `1 -> C_3 = <z> -> E_3 -> Sp_4(Z) -> 1` be Deligne's connected triple cover. For
every field `k` of characteristic `3`, `k[E_3]` is stably finite.

**Why.** `Sp_4(Z)` is finitely generated and linear, hence residually finite and LEF, so `k[Sp_4(Z)]` is
stably finite. `C_3` is a normal `3`-subgroup, so stable finiteness passes up to `k[E_3]`. The fact that
`C_3` lies in the finite residual of `E_3` doesn't matter here.

**Consequences for strict automata on E_3** (artifact Corollary 2.2):
- no strict `k`-linear automaton on `(k^n)^(E_3)` for finite `k` of characteristic `3`;
- over an alphabet `F_3^n`, no strict pair whose left-inverse identity holds formally
  (`formal-polynomial-strict-pairs-need-unstable-linearization`);
- over `F_q^m` with `q` a power of `3`, every strict pair has `deg sigma * deg tau >= q`
  (`low-degree-strict-automata-force-matrix-kaplansky-failure`);
- if `prime-field-left-inverse-pairs-are-stably-formalizable` holds at `p = 3`, `E_3` is surjunctive over
  every alphabet of size `3^n`.

**Scope.** For a prime `p != 3` and `q = p^f` with `q = 1 mod 3`, the algebra splits:
`F_q[E_3] = F_q[Sp_4(Z)] x e_chi F_q[E_3] x e_chibar F_q[E_3]`. The first factor is stably finite. The
other two are twisted group algebras of `Sp_4(Z)` with the multiplier of a section, and their stable
finiteness is open. So over `F_p` with `p != 3`, a linear counterexample on `E_3` is not excluded.
