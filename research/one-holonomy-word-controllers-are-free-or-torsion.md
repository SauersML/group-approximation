---
rg: 2
id: one-holonomy-word-controllers-are-free-or-torsion
kind: claim
title: A finite monomial controller either leaves the two-cycle holonomy free or forces a bounded return
distinct_from:
  verifier-controlled-two-cycle-is-existentially-loss-blind: that exposes the arbitrary unitary return holonomy of the bare two-cycle; this classifies every finite controller whose words see that holonomy only by a common tensor orientation.
  finite-cocycle-select-has-an-exact-power-return: that finds a finite-character countermodel for a finite SELECT packet; this proves a general exponent dichotomy for an arbitrary fixed finite flag packet and one multiplicity holonomy.
  twist-invariant-carriers-force-relative-character-kernels: that uses scalar twists to obstruct unbalanced bridge returns; this also treats exponent-balanced controllers and proves that the alternative is an algebraically bounded localized return.
---

**ESTABLISHED CONDITIONAL NO-GO.**  Consider the negative verifier sector of
a two-cycle, with return holonomy `A` as in `(VTL7)--(VTL8)`.  Let a proposed
finite controller use a fixed finite-dimensional flag packet `K` of exponent
`e`.  Assume every controller letter restricts on this sector in the common
orientation

```text
u_l |_- = F_l tensor A^(n_l),       F_l in pi(K), n_l in Z.          (OH1)
```

Then every ordinary controller word has the form

```text
rho |_- = F_rho tensor A^(n_rho).                                  (OH2)
```

For any finite list of relators there are only two possibilities.

1. **Free-holonomy branch.**  Every relator has exponent `n_rho=0` and its
   flag factor is the identity.  The relations impose no condition on `A`.
   After amplification, `A` may be a cyclic shift of arbitrarily large order,
   so every prescribed finite localized return-moment window vanishes.

2. **Torsion branch.**  Some relator has `n_rho!=0`.  Exact solvability forces
   its flag factor to be scalar.  Since `K` has exponent `e`, the relators
   force

   ```text
   A^N=1                                                       (OH3)
   ```

   for one positive integer `N` depending only on the fixed controller.
   Since the two-cycle word squares to `A` on its selected source, this is a
   bounded localized return.

The torsion branch cannot coexist with both a nonzero fixed finite-support
source `q in C[Gamma]` and an infinite-order wandering word `w` when the
localized return is a universal consequence of the group relators.  In the
left regular representation it gives

```text
(w^(2N)-1)q=0.                                                (OH4)
```

Finite support then implies `q=0` unless a positive power of `w` is the
identity.  Therefore a common-orientation finite word controller cannot close
the Fanizza wandering promotion: it either preserves the cyclic-shift
countermodels or destroys the required regular wandering normal form.

## Exact scope

The theorem does not cover a controller which makes different letters act by
noncommuting transformations of the multiplicity algebra, or whose carrier
itself depends on `A`.  Such a construction would genuinely couple verifier
loss to holonomy rather than append a finite flag test.  This is precisely the
remaining escape from the no-go.

