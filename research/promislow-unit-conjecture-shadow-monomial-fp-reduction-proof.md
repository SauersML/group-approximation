---
rg: 2
id: promislow-unit-conjecture-shadow-monomial-fp-reduction-proof
kind: route
title: Reduce an integral unit modulo a large prime and read its coefficients back
target: promislow-unit-conjecture-from-shadow-monomial-fp-units
requires:
  - promislow-integral-units-have-monomial-definite-line-shadows
  - rational-units-rescale-to-integral-units
---

Notation as in the target. For `v in Z[P]` let `|v| = max_g |v(g)|`.

**Step 1: reductions of integral units lie in `SM_p`.** The three shadows are
ring homomorphisms `Z[P] -> D(Z)` given by the same formulas over every
commutative ring (table in
`promislow-integral-units-have-monomial-definite-line-shadows`). So they commute
with reduction modulo `p`: the shadow of `v mod p` is the reduction of the
shadow of `v`. Let `v` be a unit of `Z[P]` with inverse `v'`. Then `v mod p` is a
unit of `F_p[P]` with inverse `v' mod p`. By item 1 of that claim, each shadow of
`v` is `+-t^m` or `+-t^m u` in `D(Z)`, and the reduction of such an element is
again of that form in `D(F_p)`. Hence `v mod p in SM_p`.

**Step 2: large primes see the support.** Let `p > 2|v|`. Every coefficient of
`v` is an integer in `(-p/2, p/2)`. Reduction modulo `p` is injective on those
integers and sends nonzero ones to nonzero residues. So
`supp(v mod p) = supp(v)`, and `v` is determined by `v mod p`.

**Item 2.** Suppose `v in Z[P]^x` is not `+-g`. If `|supp(v)| = 1`, then `v = c g`
with `c in Z`. The augmentation `Z[P] -> Z` is a ring homomorphism, so it sends
`v` to the unit `c` of `Z`, giving `c = +-1`, a contradiction. So
`|supp(v)| >= 2`. For `p > 2|v|`, Step 1 gives `v mod p in SM_p`, and Step 2 gives
`|supp(v mod p)| >= 2`, so `v mod p` is not `lambda g`.

**Item 1.** Let `v in Z[P]^x`, and choose a prime `p` in the given infinite set
with `p > 2|v|`. By Step 1, `v mod p in SM_p`, so by hypothesis `v mod p = lambda g`.
By Step 2, `supp(v) = {g}`, so `v = c g` with `c in Z`. As in item 2, `c = +-1`.
So every unit of `Z[P]` is `+-g`.

For `Q[P]`: `P` is torsion-free elementary amenable, so every `F_p[P]` is a
domain, as recorded in `rational-units-rescale-to-integral-units`. By item 1
there, every unit of `Q[P]` is `c v` with `c in Q^x` and `v in Z[P]^x`, hence
`lambda g`.

QED
