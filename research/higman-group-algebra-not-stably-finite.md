---
rg: 2
id: higman-group-algebra-not-stably-finite
kind: claim
title: Some matrix ring over a modular group algebra of Higman's group has a one-sided inverse that is not two-sided
artifacts:
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
---

**OPEN.** Let `H = <a,b,c,d | b^a=b^2, c^b=c^2, d^c=d^2, a^d=a^2>`. For some prime `p` and some `n >= 1`
there are `A, B in M_n(F_p[H])` with `BA = I_n != AB`.

By `higman-stable-finiteness-failure-gives-nonsurjunctivity` this refutes Gottschalk's conjecture on `H`.

## Attempts

* **One track dies if `H` has unique products (artifact Section 3).** Then `F_p[H]` is a domain, and `BA = 1`
  gives `(AB - 1)A = 0`, so `AB = 1`. The import "left-orderable groups are unique-product groups" (with
  Rivas--Triestino's left order on `H`) was not re-read by this lane. So a witness needs `n >= 2`.
* **Support filter.** Group algebras of sofic groups are stably finite over every field (Elek--Szabo, imported).
  So the supports of `A` and `B` generate a nonsofic subgroup, and by
  `nonsofic-subgroups-of-higman-group-have-free-edge-groups` it splits over nonabelian free edge groups in both
  splittings of `H`.
* **Division-ring route to the negation (artifact Section 3).** `H = G_1 *_F G_2` with `F = <a,c>` free. If
  `F_p[G_1]` and `F_p[G_2]` embed in skew fields `D_1, D_2` in which the division closures of `F_p[F]` are the same
  `F_p[F]`-field `U`, and cosets of `F` are left independent over `U`, then `F_p[H]` embeds in the coproduct
  `D_1 *_U D_2`. That coproduct is a fir (Cohn) and embeds in its universal field of fractions, so `F_p[H]` would
  be stably finite and this claim false. Where it stops: the uniqueness half. A free group algebra has many
  fields of fractions. Hughes' uniqueness theorem would identify both closures with the universal field of
  fractions of `F_p[F]` if they were Hughes-free for `F`, and that is not established for any construction of
  `D_1, D_2` here. The known division embedding of `k[H]` (Fisher--Sanchez-Peralta 3.14) is in characteristic
  zero only. `H` is perfect, so it is not locally indicable, and the Hughes-free theory does not apply to `H`
  itself.
