---
rg: 2
id: compression-gates-need-strict-unit-centralizer-chains
kind: claim
title: A compressing automorphism with a unit root forces a strictly ascending chain of unit centralizers, so rings whose unit group is Noetherian modulo the centre fail both ring gates
distinct_from:
  matricial-compression-ring-exists: that is the existence question (R1)-(R5); this is a necessary condition on (R2)-(R5) alone, with no approximation hypothesis, which kills every automorphism and every subring on every ring whose unit group is Noetherian modulo its centre.
  simple-ring-with-centralizer-compressing-automorphism: that is the simple-ring existence question (G1)+(G2); the same necessary condition applies to (G2), for every automorphism, whether or not any power is inner.
  virtually-inner-ring-automorphisms-fail-centralizer-compression: that kills automorphisms with an inner power over a matricially embeddable overring, using finite dimension of matrix models; this uses no models and no overring, and it kills automorphisms of infinite order modulo inner ones, such as the symplectic automorphisms of quantum tori.
  matricial-rings-rigidify-compression-centralizers: that forbids implementing the restriction of psi by a unit of an exactly matricial overring; this is a chain condition inside the unit group of R itself.
  subshift-compression-witnesses-need-unbounded-support-relation: that restricts subrings and roots on subshift crossed products through supports and a half-orbit index; this is ring-independent and explains why only rings with lamp-like unit groups survive.
---

**ESTABLISHED** (complete elementary proof below).

**Setting.**  `R` is a nonzero unital ring, `U = U(R)` its unit group,
`Z^x = U cap Z(R)` its central units, `psi in Aut(R)`, and `R_0 <= R` is any
subring with `psi(R_0) <= R_0`.  Finite generation is not used.  Put

```text
M = U cap C_R(R_0)        (the unit centralizer of R_0).
```

A **root** is a unit `z in M` such that `psi(z)` does not commute with some
element of `R_0`.  Equivalently, `z` fails to commute with some element of
`psi^(-1)(R_0)`.

**Theorem A (commutant expansion).**
1. `M <= psi(M)`, and `Z^x <= M`.
2. A root exists iff `M < psi(M)` strictly.  In that case
   `psi^n(M) < psi^(n+1)(M)` for every integer `n`.  So
   `... < psi^(-1)(M) < M < psi(M) < psi^2(M) < ...` is a strictly monotone
   chain of subgroups of `U`, indexed by `Z`, each containing `Z^x`.
3. A root `z` has `psi^n(z) in psi^n(M) \ psi^(n-1)(M)` for `n >= 1`.  So the
   units `psi^n(z)`, `n >= 0`, are pairwise distinct modulo `Z^x`.

**Consequences for the two ring gates.**
- In `matricial-compression-ring-exists`, (R4)+(R5) need a root.  If there
  is no root, then `psi(z)` commutes with `R_0` for every unit `z` commuting
  with `R_0`.  Then every generator `psi(z) p psi(z)^(-1) - p` of `I` is `0`,
  so `I = 0 != R`.
- In `simple-ring-with-centralizer-compressing-automorphism`, (G2) asks for a
  root of `sigma` on `(S, R)`.

So both gates require the strict chain of Theorem A(2).

**Theorem B (Noetherian unit groups die).**  Suppose `U / Z^x` satisfies the
maximal condition on subgroups.  Then no automorphism of `R`, with any
subring `R_0`, has a root.  So (R2)-(R5) and (G2) both fail on `R`.

**Corollary C (unit-generated subrings in M_c unit groups).**  Suppose
`U` satisfies the ascending chain condition on centralizers.  This holds
when `U` is linear over a field, abelian, or torsion-free hyperbolic.  Suppose
also that `R_0` is generated as a ring by `S_0 = R_0 cap U` together with
central elements.  An example is the image of a group ring `Z[H] -> R`, as in
Attempt 7 of `matricial-compression-ring-exists`.  Then `psi` has no root on
`R_0`.

**Invariant and dying step.**
- *Invariant.* The unit centralizer `M = U(R) cap C_R(R_0)`, and the position
  of `M` in the subgroup lattice of `U(R)/Z(R)^x`.
- *Dying step.* The inclusion `psi(R_0) <= R_0` is inverted by passing to
  commutants, so `M <= psi(M)`.  Any chain condition on the unit group then
  turns this inclusion into the equality `M = psi(M)`.  Once `M = psi(M)`,
  `psi(z)` commutes with `R_0` for every admissible `z`.
- Every member of the classes in Theorem B and Corollary C dies at this step,
  for every automorphism, whatever its order modulo inner automorphisms.

## Proof

**Theorem A.**
1. Since `psi` is a ring automorphism, `psi(C_R(X)) = C_R(psi(X))` for every
   subset `X`, and `psi(U) = U`.
   - So `psi(M) = U cap C_R(psi(R_0))`.
   - Since `psi(R_0) <= R_0`, every element commuting with `R_0` commutes
     with `psi(R_0)`.  Hence `M <= psi(M)`.
   - Central units commute with everything, so `Z^x <= M`.
2. A root is exactly an element `z in M` with `psi(z) notin M`, i.e.
   `psi(M) not<= M`.
   - By (1) this is equivalent to `M < psi(M)`.
   - Applying the bijection `psi^n` of `U` to `M < psi(M)` gives
     `psi^n(M) < psi^(n+1)(M)`.
   - Finally `psi^n(Z^x) = Z^x`, because `psi` preserves the centre and the
     units.
3. Since `z in M \ psi^(-1)(M)`, applying `psi^n` gives
   `psi^n(z) in psi^n(M) \ psi^(n-1)(M)`.
   - For `0 <= m < n`, we have `psi^m(z) in psi^m(M) <= psi^(n-1)(M)`.
   - The subgroup `psi^(n-1)(M)` contains `Z^x`.  So `psi^n(z)` lies outside
     the coset `psi^m(z) Z^x`.

**Theorem B.** Let `pi : U -> Ubar = U/Z^x`.
- `psi` preserves `U` and `Z^x`, so it induces an automorphism `psibar` of
  `Ubar`.
- Every `psi^n(M)` contains `Z^x`.  So `psi^n(M) = pi^(-1)(psibar^n(pi(M)))`,
  and strict inclusions are preserved by `pi`.
- If a root existed, Theorem A(2) would give a strictly ascending infinite
  chain `pi(M) < psibar(pi(M)) < psibar^2(pi(M)) < ...` of subgroups of `Ubar`.
  This contradicts the maximal condition.

**Corollary C.**
- Put `M_n = psi^n(M)` for `n >= 0`.  Since `C_R(R_0) = C_R(S_0)`, applying
  `psi^n` gives `C_R(psi^n(R_0)) = C_R(psi^n(S_0))`, with `psi^n(S_0) <= U`.
- Hence `M_n = U cap C_R(psi^n(S_0)) = C_U(psi^n(S_0))`.  So the `M_n` are
  centralizers in the group `U`.
- They ascend, by Theorem A(1) applied to `psi^n`.  By the ascending chain
  condition, `M_N = M_(N+1)` for some `N`.
- Applying `psi^(-N)` gives `M = psi(M)`.  By Theorem A(2), there is no root.

*The standard facts used.*
- For centralizers in a group, `C(C(C(X))) = C(X)`.  So `X -> C(X)` is an
  inclusion-reversing involution on centralizers, and ACC is equivalent to DCC.
- If `U <= GL_m(F)` for a field `F`, then `C_U(X) = U cap C_(M_m(F))(X)`.  The
  second factor is an `F`-subspace, so dimension gives DCC.
- In a torsion-free hyperbolic group, a centralizer is trivial, maximal
  cyclic, or the whole group.  So chains of centralizers have length at most 3.

## Classes killed by Theorem B

**(B1) Rings with central units.**  If `U = Z^x`, then `Ubar = 1`.
- This covers commutative rings.
- It also covers every ring with an exhaustive filtration
  `F_0 <= F_1 <= ...` such that `F_0` is central and the associated graded
  ring is a domain.
  - Degrees add, so a unit has degree 0 and lies in the central ring `F_0`.
  - Examples are Weyl algebras in characteristic 0 (Bernstein filtration),
    free algebras, and enveloping algebras of finite-dimensional Lie algebras
    over fields.
- Here (R4) forces `z` to be central, and `psi(z)` is central too.

**(B2) Twisted group rings with trivial units over Noetherian groups.**  Let
`k` be a commutative domain, `Lambda` a group, `c` a 2-cocycle with values in
`k^x`, and `R = k^c[Lambda]` with basis `u_lambda`.
- Suppose every unit of `R` has the form `a u_lambda` with `a in k^x`.
  - Then `a u_lambda -> lambda` is a surjective homomorphism `U -> Lambda`,
    because `u_lambda u_mu = c(lambda,mu) u_(lambda mu)`.
  - Its kernel `k^x` is central.
  - So `Ubar` is a quotient of `Lambda`.
- If `Lambda` satisfies the maximal condition on subgroups (polycyclic-by-finite),
  Theorem B applies.
- *Trivial units for bi-orderable `Lambda`.*  Let `x y = 1` with supports `A`
  and `B`.
  - For a bi-invariant order, `max A * max B` is the unique largest product
    `a b` with `a in A`, `b in B`.  Its coefficient
    `x_a y_b c(a,b)` is nonzero because `k` is a domain.  The same holds for
    the smallest product.
  - Since `xy = 1` has one-point support, the largest and smallest products
    coincide.
  - Bi-invariance then forces `min A = max A` and `min B = max B`.
- `Z^d` and every finitely generated torsion-free nilpotent group are
  bi-orderable and Noetherian.

So (B2) contains:
- every quantum torus `k_B[Z^d]`, for any coefficient domain `k`, any
  integer antisymmetric `B` and any `q`, with `u_i u_j = q^(b_ij) u_j u_i`;
- every twisted group ring of a finitely generated torsion-free nilpotent group,
  such as quantum Heisenberg rings.

The hypothesis on units is not automatic for polycyclic-by-finite groups:
the Promislow group has a nontrivial unit in `F_2[P]` (Gardam 2021).

**Why (B2) is a genuine new kill: quantum tori pass the other filters.**
Take `k = Z[q^(+-1), (q^g - 1)^(-1)]` with `q` an indeterminate and `g` the
gcd of the entries of `B`.
- *Finitely generated.*  `R = k_B[Z^d]` is generated as a ring by
  `q^(+-1)`, `(q^g - 1)^(-1)` and `u_i^(+-1)`.
- *(R1) holds.*  Map `q -> e^(2 pi i / n)` and use tensor products of
  clock-and-shift matrices, after putting `B` in Frobenius normal form.
  - Choose algebraically independent transcendentals for the radical
    variables.
  - This gives a homomorphism `R -> prod_omega M_(N_n)(C)`.
  - It is injective: a nonzero coefficient in `Z[q^(+-1)]` vanishes at only
    finitely many roots of unity, and for large `n` the finitely many
    monomials involved map to linearly independent matrices.
- *Attempt 3 of `matricial-compression-ring-exists` does not apply.*  A
  commutative quotient would need `q^g = 1`, and `q^g - 1` is a unit.
- *Many automorphisms, none with an inner power.*  `Aut(Z^d, B) cap GL_d(Z)`
  acts by graded automorphisms, often through infinite-order symplectic
  matrices.
  - Every inner automorphism fixes the grading, since units are monomial.
  - So an infinite-order `alpha` gives an automorphism with no inner power.
  - Hence `virtually-inner-ring-automorphisms-fail-centralizer-compression`
    applies only if some matricially embeddable overring implements a power of
    `psi`.  For example, the twisted group ring of `Z^d semidirect_alpha Z`
    would do, but its matricial embeddability is unverified.
- Theorem B nevertheless kills every automorphism, every subring and every
  root on every such ring.  The proof reduces to the fact that in `Z^d` a
  subgroup `M` with `M <= alpha(M)` for `alpha in GL_d(Z)` already satisfies
  `M = alpha(M)`.

## What a surviving ring must look like

Combining Theorem A with Corollary C gives three requirements.
- `U(R)/Z(R)^x` must contain an infinite strictly ascending chain of images of
  unit centralizers, all translates of one of them under `psibar`.
- `psibar^(-1)` must map the subgroup `psibar(Mbar)` properly into itself.
- If `R_0` is unit-generated, `U(R)` must fail the chain condition on
  centralizers.  In particular `U(R)` is not linear over a field and not
  torsion-free hyperbolic.

The rings still live in the cone escape Theorem B, because their unit groups
modulo the centre are not Noetherian:
- the subshift crossed products `LC(X,F_q) semidirect Z` over infinite minimal
  subshifts.  Their centre is `F_q`, and their unit groups contain the
  infinitely generated abelian group `LC(X,F_q^x)` and the topological full
  group;
- Leavitt algebras, whose unit groups contain Thompson's group `V`;
- the twisted lamp ring of Attempt 7.  There the Clifford lamps `c_x` are
  noncentral, and they give an infinitely generated elementary abelian
  subgroup of `Ubar`.

The first two unit groups contain infinite restricted direct sums of finite
symmetric groups, permuting infinitely many disjoint clopen sets.  So they
also fail the chain condition on centralizers, which passes to subgroups, and
Corollary C does not apply either.  In this sense only rings with lamp-like
unit groups survive.  The gate must be attacked there; Noetherian-graded
constructions such as quantum tori and quantum nilpotent group rings are
excluded outright.
