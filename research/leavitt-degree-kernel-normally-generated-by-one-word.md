---
rg: 2
id: leavitt-degree-kernel-normally-generated-by-one-word
kind: claim
title: A degree-m word normally generating the kernel over the Leavitt unit group
distinct_from:
  kl-violating-equation-over-leavitt-unit-group: that asks for any nonsingular equation over the same group killing some coefficient; this asks for the specific maximal form -- a word whose ambient normal closure is the whole degree-m kernel, which kills every coefficient at once. It is sufficient for that claim and strictly stronger.
  uniform-normal-rank-certificate-for-degree-kernels: that asks for a uniform reason no word ever normally generates such a kernel, which would prove the conjecture; this asks for one word over one group that does. Opposite answers to the same question.
  leavitt-group-algebra-not-stably-finite: that asks for a one-sided inverse pair of matrices over the group algebra of the same group, a ring-theoretic finiteness failure; this asks for a word in the group's free product with an infinite cyclic group, and neither statement supplies or excludes the other.
  leavitt-unit-group-nonsurjunctive: that asks for an injective non-surjective cellular automaton over the same group, refuting Gottschalk; this asks for a normal-generation identity refuting Kervaire--Laudenbach. Same group, unrelated conjectures, and no implication is known in either direction.
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Exhibit `m >= 1` and a word `w in N_m = ker(R^x * <t> -> C_m)` with
`deg_t(w) = m`, where `R^x = L_(F_2)(1,2)^x`, such that

    <<w>>_{R^x * <t>}  =  N_m .

By part (b) of `kl-simple-failure-leaves-only-the-cyclic-quotient` — which
needs no simplicity, only `R^x != 1` — this makes
`(R^x * <t>)/<<w>> = C_m`, so every coefficient dies and
`kl-violating-equation-over-leavitt-unit-group` follows.

## Why state the maximal form rather than the general one

Because over a group like this one the general form is not actually weaker in
any usable way.  `R^x` is perfect
(`leavitt-gl-equals-el-and-perfect-unit-group`); if it is also simple, then by
part (a) of the same claim *any* violation over it is already of this maximal
form, and asking for less buys nothing.  If it is not simple, this is a
genuine strengthening — but it is also the only form for which the search has
a definite target, namely a single normal-generation identity rather than an
unspecified element to kill.

## Attempts

1. **First-homology certificate.**  Compute in `N_m^ab` and try to select `w`
   by its class.  *Dies* at `degree-kernel-abelianization-is-infinite-cyclic`:
   `R^x` is perfect, so `N_m^ab = Z` and *every* degree-`m` word is a
   generator.  The test passes for all candidates and therefore selects none.
   Recorded as `leavitt-kl-violation-via-fox-calculus`.
2. **Screen the group by its subgroups.**  *Dies* at
   `kl-counterexample-absorbs-any-countable-group`.  Recorded as
   `kl-counterexample-screening-by-local-subgroup-structure`.
3. **Use the explicit atlas relators.**  *Deferred*, and the audit's advice is
   to stop repeating first-homology tests on them: a finite list of relators
   in a chart presentation is not a relative relator, and the atlas source's
   own kernel `R/[R, R]` bears on one-relator compression of that source, not
   on `N_m`.
4. **Search a finite nonabelian or solvable quotient of `N_m`.**  *Impossible*
   by `leavitt-degree-kernel-quotient-tests-are-procyclic`: the Leavitt unit
   group is perfect and has no finite quotients, so every finite or solvable
   image of `N_m` kills all coefficient free factors and is cyclic; every
   degree-`m` candidate maps to its generator.  If a candidate fails to
   normally generate, the quotient by its ambient normal closure is necessarily
   infinite, perfect, and has no finite quotients.  A Peiffer/crossed-module
   test must therefore retain a genuinely nonsolvable coefficient image.
5. **Put a normally generating Leavitt root next to the variable power.**
   The explicit candidate `w=r t^2`, where the involutive root `r` normally
   generates `G`, fails at
   `leavitt-normal-root-square-equation-has-amalgam-countermodel`:
   the relative quotient is `G *_(C_2) C_4`, and the degree-kernel quotient is
   the concrete nonsolvable group `G *_(C_2) G`.  Normal generation of `r`
   inside `G` does not kill `r` after it is identified with `t^2`; a candidate
   must use separated variable blocks and distinct coefficient conjugacy data.
6. **Use the shortest such two-block word.**  This also fails.  For adjacent
   normal-generating involutive roots `r=x_12(1)`, `s=x_23(1)`, the word
   `r t s t` becomes `y^2=rs` after `y=ts`; see
   `two-root-two-block-kl-word-is-cyclic-amalgam`.  Its obstruction quotient
   is `G *_(C_4) G`.  A viable word must avoid reduction to a single root
   adjunction, so at least three blocks or an asymmetric sign pattern is the
   next honest search space.
7. **Use the minimal asymmetric three-block root cycle.**  The word
   `x_12(1) t x_23(1) t x_31(1) t^(-1)` has depth pattern `(0,1,2)` and no
   solution inside `GL_3(F_2)`, but all its coefficients lie in that finite
   subgroup.  By `three-root-asymmetric-kl-word-has-finite-core-pushout`, the
   full quotient is the amalgam `G *_(GL_3(F_2)) P_H` and still embeds `G`.
   Constant root packets and finite prefix packets are therefore categorically
   the wrong coefficient source; the coefficients must generate a subgroup
   outside every class where KL is already known.
8. **Impose the universal low-length fence before searching.**  By
   `length-five-kl-fence-for-leavitt-equations`, every nonsingular word of
   variable length at most five preserves the coefficient group, even when
   its coefficients generate all of `G`.  In particular both length-five
   types `++++-` and `+++--` are settled universally by Evangelidou.  The
   first unresolved full-support shapes occur at length six and, after
   symmetries, have sign type `+++++-` or `++++--`.  No shorter self-similar
   coefficient packet can work.
9. **Audit the first full-support length-six word.**  The explicit word
   `x_12(s_0)t x_12(s_1)t x_12(t_0)t p t x_12(t_1)t^(-2)` from
   `leavitt-length-six-full-support-torsion-candidate` has degree two and its
   five nonidentity coefficients generate all of `G`.  The two sign-change
   coefficients are involutions, so it evades exactly the Stallings and
   Clifford--Goldstein torsion-free gates.  In
   `N_2=G_0*G_1*<z>` it becomes
   `a_0 b_1 z c_0 d_1 z e_0 z^(-1)`; its `t`-translate is
   `a_1 z b_0 c_1 z d_0 e_1 z^(-1)`.  Each relator alone preserves
   `G_0*G_1` by the universal length-three theorem.  The next concrete task
   is to decide whether this explicit pair jointly normally generates `N_2`.
   The one-copy-killing and obvious twisted-diagonal retractions fail by the
   checked computations in that node, and the pair is not staggered because
   both relators occupy the same height interval `[0,2]`.
10. **Reality check, recorded because this claim reads more tractable than it
   is.**  Establishing it refutes `kervaire-laudenbach-nonsingular-conjecture`
   outright, and no violating equation is known over any group whatsoever.
   The honest reading — inherited from
   `kl-violating-equation-over-leavitt-unit-group` and unchanged by the
   sharpening — is that this is a falsification instrument and a consistency
   constraint, not a plausible line of attack.
