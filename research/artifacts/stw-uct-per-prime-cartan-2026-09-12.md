---
title: STW Problem II prime by prime - Barlak--Li II Theorem 4.16, the at-most-one-prime dichotomy, and the equivariant bootstrap fence (uct-problem lane, 2026-09-12)
---

# Scope

Lane `uct-problem` (relaunch of `stw-uct`) on `stw99-problem-ii-nuclear-uct`.
This artifact records the sources read on 2026-09-12, the per-prime import, and
the derivations wired from it.  Texts were extracted on MSI with ghostscript
`txtwrite` from the arXiv PDFs.  Theorem numbers below are from the PDFs.

# 1. Barlak--Li, *Cartan subalgebras and the UCT problem, II*, arXiv:1704.04939v2

* **Theorem 1.2** (p. 3).  For `n ≥ 2`, a unital UCT Kirchberg algebra `A` and an
  outer approximately representable `α : Z_n ↷ A` with `A ⋊_α Z_n` absorbing
  `M_(n^∞)`: the crossed product satisfies the UCT iff an `α`-homogeneous inverse
  semigroup model with Cantor-spectrum Cartan subalgebra exists iff some Cartan
  subalgebra `C ⊆ A` has `α(C) = C`.
* **Corollary 4.15** (p. 26).  "Let p ≥ 2 be a prime number, n ≥ 1 a natural
  number and q = p^n.  Let α : Z_q ↷ O_2 be an outer strongly approximately inner
  action.  Then the following are equivalent (i) O_2 ⋊_α Z_q satisfies the UCT;
  (ii) [homogeneous inverse semigroup model]; (iii) there exists some Cartan
  subalgebra C ⊆ O_2 such that α(C) = C."  Proof in the source:
  Pimsner--Voiculescu makes `K_*(O_2 ⋊_α Z_q)` uniquely `p`-divisible and in Cuntz
  standard form (Izumi I, Lemma 4.4), so the crossed product absorbs `M_(p^∞)`;
  `α` is approximately representable (Izumi I, Theorem 4.6); Theorem 4.12 applies.
* **Theorem 4.16** (pp. 26--27).  "Let p ≥ 2 a prime number.  The following
  statements are equivalent: (i) Every separable nuclear C*-algebra A that is
  KK-equivalent to A ⊗ M_(p^∞) satisfies the UCT; (ii) [homogeneous inverse
  semigroup models for every outer strongly approximately inner Z_p-action on
  O_2]; (iii) every outer strongly approximately inner Z_p-action on O_2 fixes
  some Cartan subalgebra B ⊆ O_2 globally."  The sentence before it: "A similar
  result for the case p = 2 can be found in [1, Theorem 5.8]", where [1] is
  Barlak--Li I.
  * (i) ⟹ (ii): `O_2 ⋊_α Z_p` is a unital `M_(p^∞)`-absorbing Kirchberg algebra,
    so it satisfies the UCT by (i); Corollary 4.15.
  * (iii) ⟹ (i): Kirchberg [22, Theorem I] replaces `A` by a unital
    `M_(p^∞)`-absorbing Kirchberg algebra `Ã`.  Barlak--Szabó [2, Proposition 4.14]
    give an outer approximately representable `γ : Z_p ↷ O_2` with
    `O_2 ⋊_γ Z_p ~_KK M_(p^∞)^(p-1)`.  Under `Ã ⊗ O_2 ≅ O_2` put `β = id_Ã ⊗ γ`;
    then `O_2 ⋊_β Z_p ≅ Ã ⊗ (O_2 ⋊_γ Z_p) ~_KK Ã^(p-1)`.  An invariant Cartan
    subalgebra for `β` gives the UCT for the crossed product ([1, Proposition 3.4]),
    hence for `Ã`.
* **Corollary 4.17** (= Theorem 1.4): Problem II iff statement (iii) at `p = 2`
  and `p = 3`.  "This follows immediately from Theorem 4.16 and
  [2, Proposition 4.16]."  [2] is Barlak--Szabó, *Rokhlin actions of finite
  groups on UHF-absorbing C*-algebras*, Trans. Amer. Math. Soc. 369 (2017).
* Remark 4.18 points to Blackadar's *K-theory for operator algebras*, 23.15.12,
  for similar characterizations "without further details".

**Stale graph text this corrects.**  `uct-for-three-infinity-absorbing-nuclear-algebras`
said no odd-prime analogue had been checked from the source, and
`o2-z3-actions-fix-a-cartan-subalgebra` said no source read proves the half at 3
equivalent to the order-three dynamical statement.  Theorem 4.16 at `p = 3` is
that equivalence.

# 2. Meyer--Nadareishvili, arXiv:2604.12529v2 (v1 14 Apr 2026, v2 25 Jun 2026)

*A universal coefficient theorem for actions of finite cyclic groups of
square-free order on C\*-algebras.*  Read: abstract, introduction, Theorem 1.1,
start of Section 2.

* The equivariant bootstrap class `B^G` "is defined to consist of all
  G-C*-algebras that are KK^G-equivalent to an action on a Type I C*-algebra".
* Theorem 1.1: for `G` finite cyclic of square-free order there is a stable
  homological functor `U^G_C` to countable exact `Z/2`-graded modules over a ring
  `K_G` with a natural short exact UCT sequence for `A ∈ B^G`; isomorphisms of
  invariants lift to `KK^G`-equivalences inside `B^G`.
* "It was shown in [7] that any KK^G-equivalence class in the equivariant
  bootstrap class is represented by a pointwise outer action on a Kirchberg
  algebra, still in the bootstrap class.  Gabe and Szabó [5] have shown that two
  such actions are cocycle conjugate if and only if they are KK^G-equivalent."

The paper does not mention the UCT problem, Cartan subalgebras or Barlak--Li.
Its bearing is recorded in `bootstrap-class-zp-actions-on-o2-fix-a-cartan`.

# 3. Barlak--Szabó, arXiv:1712.00823v2 (Groups Geom. Dyn. 14 (2020))

Read: abstract and introduction only.  "We show that the UCT problem for
separable, nuclear C*-algebras relies only on whether the UCT holds for crossed
products of certain finite cyclic group actions on the Razak--Jacelon algebra."
The introduction recalls Kirchberg's reduction to trivial-K Kirchberg algebras,
the Cartan characterization, Dadarlat's reduction to tracially AF algebras with
the K-theory of `Q`, and that a variant of Blackadar 23.15.12 reduces the problem
to crossed products of `O_2` by certain circle actions.  Not wired: it is another
restatement with no new attack surface for this lane.

# 3b. Barlak--Szabó, arXiv:1403.7312 (Trans. Amer. Math. Soc. 369 (2017))

*Rokhlin actions of finite groups on UHF-absorbing C\*-algebras.*  Read: Remark
4.13 through the start of the proof of Theorem 4.17 (pp. 25--26).

* **Proposition 4.14.**  For a natural number `p ≥ 2` there is a locally UCT
  Kirchberg-representable action `γ : Z_p ↷ O_2` with `O_2 ⋊_γ Z_p` KK-equivalent
  to `M_(p^∞)^(φ(p))`.
* **Proposition 4.16.**  "Let A be a separable C*-algebra, and let p, q ≥ 2 be two
  relatively prime natural numbers.  If both M_(p^∞) ⊗ A and M_(q^∞) ⊗ A satisfy
  the UCT, then so does A."  Proof: `Z_(p^∞,q^∞) ⊗ A` is an extension of
  `M_(p^∞) ⊗ A ⊕ M_(q^∞) ⊗ A` by `C_0(0,1) ⊗ M_(p^∞) ⊗ M_(q^∞) ⊗ A`, and the
  Jiang--Su algebra is a stationary inductive limit of `Z_(p^∞,q^∞)`.
* **Theorem 4.17.**  For two primes `p, q` the following are equivalent: (1) every
  separable nuclear C*-algebra satisfies the UCT; (2) every unital Kirchberg
  algebra does; (3) for pointwise outer, locally Kirchberg-representable actions
  of `Z_p` and of `Z_q` on `O_2`, both crossed products satisfy the UCT; (4) the
  same for `Z_(pq)`.

**Credit correction.**  `coprime-uhf-stabilizations-detect-uct` said no source
read states (CU1).  Proposition 4.16 is its forward direction for UHF types `p^∞`
and `q^∞`, by the same dimension-drop argument.  The node's credit is corrected.

# 4. What this lane wired

* `barlak-li-p-half-iff-zp-actions-fix-cartan` (literature, with `-citation`):
  Corollary 4.15 and Theorem 4.16.
* `uct-three-half-via-z3-actions-on-o2`: route into
  `uct-for-three-infinity-absorbing-nuclear-algebras`, the twin of
  `uct-two-half-via-z2-actions-on-o2`.
* `bootstrap-class-zp-actions-on-o2-fix-a-cartan` (derivation, with `-proof`):
  an outer strongly approximately inner `Z_(p^n)`-action on `O_2` that is
  equivariantly KK-equivalent to an action on a type I algebra fixes a Cartan
  subalgebra (descent, type I crossed products, Corollary 4.15).  So every action
  that equivariant K-theoretic classification can describe is harmless, and a
  counterexample lies outside the equivariant bootstrap class.
* `o2-zp-cartan-fixing-all-primes-or-at-most-one` (derivation, with `-proof`):
  Cartan-fixing holds at all primes or at most one, and any two primes decide
  Problem II.  Item 1 is Barlak--Szabó Theorem 4.17 in Cartan form.
* Stale text corrected in `uct-for-three-infinity-absorbing-nuclear-algebras`,
  `o2-z3-actions-fix-a-cartan-subalgebra` and
  `coprime-uhf-stabilizations-detect-uct`.

# 5. Assessment

No attack in this lane has traction on either side of Problem II.

* **Negative side.**  A witness must be an outer strongly approximately inner
  `Z_p`-action on `O_2` outside the equivariant bootstrap class, at all primes but
  at most one.  The repository's rigidity mechanisms do not reach it.  The
  compression results behind the non-MF and nonsofic theorems live on
  non-amenable groups, whose group C\*-algebras are not nuclear.  Ozawa's
  Kazhdan-projection construction (arXiv:2609.08892) yields an MF algebra with
  only non-faithful tracial states, not a faithful non-quasidiagonal trace on a
  nuclear algebra as `stw99-ii-implies-ix1` would need.
* **Positive side.**  Every reduction ends at the same coherence step, with no
  new input: the intersection algebra for complexity rank one, a Cartan
  subalgebra invariant under an exotic automorphism, or `[id_A] = 0` from
  `K_*(A) = 0`.
