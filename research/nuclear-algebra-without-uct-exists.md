---
rg: 2
id: nuclear-algebra-without-uct-exists
kind: claim
title: Some separable nuclear C*-algebra does not satisfy the UCT (negative answer to STW Problem II)
distinct_from:
  stw99-problem-ii-nuclear-uct: that is the positive assertion; this is its negation, which lands as a refutation of it when established.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
  - research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md
---

**OPEN.**  There is a separable nuclear C\*-algebra that is not KK-equivalent to
any commutative C\*-algebra.  If established, this refutes
`stw99-problem-ii-nuclear-uct`.

**What a witness must look like** (all from established nodes):

* After Kirchberg's reduction it can be taken to be a unital Kirchberg algebra
  `A` with `K_*(A) = 0` and `A ≇ O_2`, i.e. `[id_A] ≠ 0` in `KK(A, A)`
  (`kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras`).
* It has no Cartan subalgebra and is not the reduced algebra of any nuclear
  twisted étale groupoid (`barlak-li-cartan-subalgebras-force-uct`).  If it is
  `O_2 ⋊_α Z_p`, then `α` leaves no Cartan subalgebra invariant
  (`cartan-respecting-o2-automorphisms-give-uct-crossed-products`).
* At every prime `r` except at most one, some outer strongly approximately inner
  `Z_r`-action on `O_2` fixes no Cartan subalgebra
  (`o2-zp-cartan-fixing-all-primes-or-at-most-one`).  Each such action is
  `KK^(Z_r)`-equivalent to no action on a type I algebra
  (`bootstrap-class-zp-actions-on-o2-fix-a-cartan`).
* It does not decompose over nuclear UCT algebras (`willett-yu-decomposability-forces-uct`).
  As a trivial-K Kirchberg algebra it has weak complexity rank one but not
  complexity rank one.
* Its UCT-support `𝒫(A)` is a proper filter or empty
  (`coprime-uhf-stabilizations-detect-uct`): `A ⊗ M_{p^∞}` satisfies the UCT for
  at most one prime `p`.  If `[id_A]` is torsion of order `n`, the filter
  contains the prime divisors of `n`
  (`torsion-kk-identity-dies-after-uhf-absorption`).
* Through `stw99-ii-implies-ix1`, any separable nuclear algebra with a faithful
  trace that is not quasidiagonal is already a witness.

## Attempts

* **Cartan-respecting automorphisms of `O_2`.**  Crossed products of `O_2` by
  finite-order gauge automorphisms from the normalizer of `D_2` (Thompson `V`) or
  by tensor flips satisfy the UCT.  Dead: invalidates
  `non-uct-witness-from-cartan-respecting-automorphism`.
* **Skandalis-type failure of K-nuclearity.**  The known non-UCT algebras,
  `C*_r(Γ)` for infinite hyperbolic Kazhdan `Γ`, fail K-nuclearity.  Every
  nuclear algebra is K-nuclear, so this mechanism cannot occur.  Dies at
  nuclearity.
* **Via quasidiagonality.**  A nuclear algebra with faithful trace that is not
  quasidiagonal would be a witness (`stw99-ii-implies-ix1`), but no such
  algebra is known.  For crossed products of unital algebras by finite groups,
  quasidiagonality of invariant traces transfers
  (`stw10-finite-crossed-products-preserve-amenable-and-qd-traces`).  A faithful
  quasidiagonal trace makes a nuclear algebra MF, hence quasidiagonal, so
  finite crossed products of unital nuclear algebras carrying an invariant
  faithful quasidiagonal trace give no candidate.  Not pursued further.
* **Equivariant K-theoretic classification.**  Köhler's UCT for `Z/p`, its
  square-free extension (Meyer--Nadareishvili, arXiv:2604.12529v2), Meyer's range
  result and the Gabe--Szabó dynamical Kirchberg--Phillips theorem classify the
  pointwise outer cyclic actions in the equivariant bootstrap class.  Every
  strongly approximately inner one of prime power order fixes a Cartan subalgebra
  (`bootstrap-class-zp-actions-on-o2-fix-a-cartan`), so no action these tools
  describe gives a witness.  Dies at the boundary of the equivariant bootstrap
  class.
* **Property (T) rigidity from this repository.**  The compression mechanisms
  behind the non-MF and nonsofic results live on non-amenable groups, whose
  group C\*-algebras are not nuclear.  Ozawa's Kazhdan-projection construction
  (arXiv:2609.08892, imported as `hyperfinite-factor-not-quasidiagonal`) yields an
  MF algebra with only non-faithful tracial states, so it supplies no faithful
  non-quasidiagonal trace for `stw99-ii-implies-ix1`.  Dies at nuclearity and
  faithfulness.
