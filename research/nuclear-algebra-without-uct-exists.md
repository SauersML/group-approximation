---
rg: 2
id: nuclear-algebra-without-uct-exists
kind: claim
title: Some separable nuclear C*-algebra does not satisfy the UCT (negative answer to STW Problem II)
distinct_from:
  stw99-problem-ii-nuclear-uct: that is the positive assertion; this is its negation, which lands as a refutation of it when established.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
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
