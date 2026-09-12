---
rg: 2
id: kl-holds-over-thompson-v
kind: claim
title: Every nonsingular one-variable equation over Thompson's group V injects its coefficients
root: true
refuted_by: [kl-violating-equation-over-thompson-v]
distinct_from:
  kl-holds-over-binary-leavitt-unit-group: that is the positive statement over the binary Leavitt unit group, which contains V; it implies this, and this does not imply it.
  kervaire-laudenbach-nonsingular-conjecture: that quantifies over all coefficient groups; this is the single coefficient group V, a finitely presented infinite simple group with torsion, where no known positive theorem applies.
  kervaire-laudenbach-holds-for-hyperlinear: that is the theorem for hyperlinear coefficient groups; V is not known to be hyperlinear.
---

**OPEN.** For Thompson's group `V`, every `w in V * <t>` with
`deg_t(w) != 0` gives an injective coefficient map
`V -> (V * <t>)/<<w>>`.

*Marked root* because it heads the positive side of the V decision, which
nothing else consumes. It matters as a necessary condition for
`kl-holds-over-binary-leavitt-unit-group`.

## Necessary for the Leavitt positive root

`thompson-v-kl-from-leavitt-kl`: injectivity of the coefficient map passes to
every subgroup containing the coefficients, and `V <= R^x`. So any proof that
the binary Leavitt unit group satisfies Kervaire--Laudenbach proves this
claim. Put the other way, a positive Leavitt proof must solve every
nonsingular equation over V.

## Attempts

1. **Hyperlinearity.** Route `thompson-v-kl-from-hyperlinearity`. It is open
   with `thompson-v-hyperlinear`.
2. **Torsion-free and locally indicable theorems.** Dead.
   - V contains every finite group, as permutations of the leaves of a
     complete prefix code. So it has torsion, and Klyachko's unimodular
     theorem (`klyachko-kl-holds-for-torsion-free`) does not apply.
   - V is perfect and nontrivial, so it has no surjection onto `Z` and is not
     locally indicable. Howie's theorem for locally indicable coefficient
     groups (J. Reine Angew. Math. 324 (1981), 165--174, as recorded in
     Klyachko--Thom, Algebr. Geom. Topol. 17 (2017), Section 1) does not
     apply to V.
3. **Finite quotients and unitary roots.** Dead.
   - V is infinite and simple (`thompson-v-finitely-presented-infinite-simple`).
   - V has no nontrivial finite-dimensional unitary representation
     (`thompson-v-has-no-nontrivial-fd-unitary-representation`).
   - So a Gerstenhaber--Rothaus root can be transported only through the
     trivial representation. By `nonsingular-adjunction-preserves-approximation-radicals`
     the kernel of the coefficient map lies in `Rad_hyp(V)`, which is `1` or
     `V`. The bound decides nothing unless V is hyperlinear.
4. **Word-shape theorems.** Partial. The fences that hold over every group
   hold over V:
   - variable length at most five (`length-five-kl-fence-citation`);
   - one-sign words (Levin's positive-equation theorem, as cited in
     `length-five-kl-fence-citation`);
   - at least four light same-sign corners (`kl-four-same-sign-corner-words-inject`);
   - small-cancellation words (`kl-small-cancellation-words-inject-every-coefficient-group`).

   None of them uses a property of V, and together they leave infinitely many
   sign patterns open.
5. **Homology.** Blind. V is integrally acyclic (Szymik--Wahl, *The homology
   of the Higman--Thompson groups*, Invent. Math. 216 (2019), 445--518,
   arXiv:1411.5035: "We prove that Thompson's group V is acyclic").
   - For every `w` of degree `m`, the relative complex
     `X_w = K(V,1) v S^1 u_w e^2` has `H_1 = Z/|m|` and `H_k = 0` for
     `k >= 2`, whether or not `w` violates.
   - A violation collapses `V_w` to `C_|m|`
     (`kl-simple-failure-leaves-only-the-cyclic-quotient`). The universal
     cover of `X_w` is then `|m|` copies of `K(V,1)` joined by an `|m|`-cycle
     with `|m|` two-cells, so `pi_2(X_w) = H_2 = Z^(|m|-1)`. At `m = +-1`,
     `X_w` is contractible.
   - `H_2(V) = 0`, so Schur injectivity over V is vacuous. No homological
     invariant of the adjunction separates a violation from a solvable
     equation.
