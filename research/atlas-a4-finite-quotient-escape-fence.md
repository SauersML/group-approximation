---
rg: 2
id: atlas-a4-finite-quotient-escape-fence
kind: claim
title: Every nontrivial finite packet-collision quotient is already a root-ellipse countermodel
distinct_from:
  atlas-a4-packet-collision-quotient-audit: that gives a conditional fork when the entire abstract quotient is finite; this proves that every nontrivial finite quotient, however small, lies on the countermodel side and quantifies its root-ellipse value.
  atlas-a4-root-ellipse-exact-tracial-escape: that constructs an escape in an arbitrary finite factor from the canonical quotient trace; this identifies exactly what residual finiteness or a single finite quotient would do in matrices.
---

Put

```text
Gamma_A4=(A8*A8)/<<thirty A4 packet words,q_19243>>.
```

Then:

1. `Gamma_A4` is infinite and nonamenable.  Indeed, all thirty packet words
   and `q_19243` are genuine relations of the canonical two-chart map, so
   `Gamma_A4` surjects onto the binary Leavitt unit group.  That quotient is
   infinite, has property `(T)`, and is nonsofic; in particular it is
   nonamenable.
2. Every homomorphism from `Gamma_A4` to a finite group is either trivial on
   both chart factors or injective on both chart factors.
3. Every **nontrivial** finite quotient supplies an exact finite-dimensional
   packet-plus-collision model with regular `A8` margins and root-ellipse
   value at least

   ```text
   S^2+S x_12+x_12^2 >= 1.                            (A4-FQ-ESCAPE)
   ```

In particular any nontrivial finite quotient refutes the proposed `3/128`
root-ellipse ceiling.  Therefore residual finiteness of `Gamma_A4` would
refute that ceiling, while truth of the ceiling would force `Gamma_A4` to
have **no nontrivial finite quotients**.  The amenable/hyperfinite shortcut is
already impossible; the remaining CE question cannot be settled by merely
showing that the abstract quotient is residually finite or amenable.

This is a fence, not a CE exclusion.  A nonamenable group can still be
hyperlinear, and the Leavitt quotient's lack of finite quotients does not
prevent `Gamma_A4` from having other finite quotients which do not factor
through it.
