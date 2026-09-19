---
rg: 2
id: leavitt-support-thirteen-from-ulie-ranks
kind: route
title: Augmentation forces odd support, the ULIE ranks kill 3 to 11, and support one is trivial
target: leavitt-rank-three-lift-inverse-support-thirteen
requires:
  - leavitt-rank-three-unit-lift
  - dykema-heister-juschenko-bounded-rank-direct-finiteness
  - binary-leavitt-algebra-not-directly-finite
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

## Why sufficient

Write `n = |supp B|` and suppose `t~ B = 1`, with `|supp t~| = 3` supplied by
the first prerequisite.

**Parity.**  The augmentation `eps : F_2[R^x] -> F_2` sends an element to the
parity of its support.  `eps(t~) = 1`, so `eps(B) = eps(t~)eps(B) = eps(1) = 1`
and `n` is **odd**.  Every even `n` is gone.

**`n = 1`.**  Then `B = [h]` for a single unit `h`, so `t~ = [h^-1]` has
support one, contradicting support three.  (This case must be argued
separately: the imported rank statement is defined only for ranks at least
two.)

**`3 <= n <= 11`.**  The rank pair `(3, n)` is in the range settled over `F_2`
by the second prerequisite, so `t~ B = 1` gives `B t~ = 1`.  Applying the
evaluation homomorphism `pi` to both equations,

    t_0 pi(B) = 1     and     pi(B) t_0 = 1,

so `t_0` is invertible in `R`.  But a two-sided inverse `c` of `t_0` satisfies
`c = c(t_0 s_0) = (c t_0) s_0 = s_0`, hence `s_0 t_0 = 1`, contradicting the
third prerequisite.

The remaining odd values start at 13.

## Note on the shape of the argument

The three prerequisites do genuinely different work and none is decorative:
the lift fixes the left rank at exactly 3, which is what puts the pair inside
the computed range; the imported computation upgrades one-sided to two-sided
in that range; and the Leavitt defect is what makes two-sided invertibility
absurd.  Drop any one and the bound is not available.
