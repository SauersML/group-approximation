---
rg: 2
id: bell-free-abelian-circle-qd-citation
kind: route
title: Import Bell's quasidiagonality theorem for free abelian circle actions
target: bell-free-abelian-circle-crossed-products-are-qd
requires: []
artifacts:
  - research/artifacts/stw11-bell-circle-actions-primary-source-2026-08-30.md
---

Apply Jamie Bell, *Crossed product C-star algebras associated with non-minimal
actions on the circle*, arXiv:2604.18410v2 (2026-07-07), Theorem 3.14
(Theorem A(iii)).

The theorem assumes exactly a free action on the circle by a countably
infinite discrete abelian group `G` and concludes that
`C(T) rtimes G` is quasidiagonal.  Bell uses the full crossed product; since
`G` is abelian and hence amenable, this is canonically the reduced crossed
product as well.

Minimality is not added: Theorem 3.14 handles both the minimal and
non-minimal cases.  Conversely, neither countability, infinitude,
discreteness, abelianness, freeness, nor the circle coefficient space is
dropped.  Remark 3.15 says that AF embeddability has not been verified in the
non-minimal case, so this route does not promote quasidiagonality to that
stronger conclusion.
