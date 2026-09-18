---
rg: 2
id: hmf5-forces-higman-to-have-no-amenable-quotient
kind: claim
title: Higman's operator-norm collapse is equivalent to having no nontrivial MF quotient, so any proof of it shows that Higman's group has no amenable quotient, an open question of Helfgott--Juschenko
distinct_from:
  higman-four-cycle-intrinsic-mf-seed: that is the open collapse statement (HMF3)/(HMF5) itself; this proves that the statement is equivalent to a quotient-theoretic one, and that it implies the open no-amenable-quotient property of Higman's group.
  nontrivial-higman-quotients-are-not-locally-elementary-amenable: that unconditionally excludes nontrivial quotients inside the finite-quotient class D (residually finite, elementary amenable, and local versions); this shows that the collapse statement would exclude every amenable, residually amenable or locally-embeddable-into-amenable quotient, which D does not reach.
  base-two-exponential-permutations-iff-sofic-higman-quotient: that makes a nontrivial sofic quotient equivalent to exponential permutations, and notes that an amenable quotient would give one; this ties the same amenable-quotient question to the operator-norm collapse instead, from the opposite side.
  amenable-implies-operator-mf: that is the imported theorem that amenable groups are MF; this applies it to the quotients of one finitely presented group.
artifacts:
  - research/hmf5-forces-higman-to-have-no-amenable-quotient-proof.md
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

**ESTABLISHED** by `hmf5-forces-higman-to-have-no-amenable-quotient-proof`.
The proof is elementary apart from the imported
[[amenable-implies-operator-mf]]. No novelty is claimed for the equivalence.
The point is what it implies for the program.

**Setting.** `Hig = <g_0,...,g_3 | g_i g_(i+1) g_i^(-1) = g_(i+1)^2>` as in
[[higman-four-cycle-intrinsic-mf-seed]]. Put `x_i = g_i^(-1)`. This turns the
relations into `x_(i+1)^(x_i) = x_(i+1)^2`, which is the presentation `H4` of
[[nontrivial-higman-quotients-keep-all-four-bs-subgroups]]. Since
`||U^(-1)-1|| = ||U-1||`, the collapse statements below read the same in
either presentation.

"MF" means operator MF in the repository convention (`IsOperatorMF`): there is
an injective homomorphism into the unitary corona
`prod_n U(k_n) / {(u_n) : ||u_n - 1|| -> 0}`.

**Statement.**

1. **Equivalence.** The following are equivalent.
   - (a) `(HMF5)`: for every `epsilon > 0` there is `delta > 0` such that every
     finite-dimensional unitary tuple with Higman relator defect at most
     `delta` has `max_i ||U_i - 1|| < epsilon`. Equivalently `(HMF3)`.
   - (b) `(HMF4)`: `Rad_MF(Hig) = Hig`. That is, every homomorphism from `Hig`
     to a norm matrix corona unitary group is trivial.
   - (c) No nontrivial quotient of `Hig` is MF.
   - (d) No nontrivial quotient of `Hig` is locally embeddable into MF groups.
2. **The collapse implies (NAQ).** Assume (a). Then `Hig` has no nontrivial
   quotient that is any of the following:
   - amenable;
   - residually amenable;
   - locally embeddable into amenable groups;
   - a subgroup of the unitary group of an MF C*-algebra.

   The first of these, (NAQ), is the open question that Helfgott and Juschenko
   raise about `H4`: "It is not known whether it has amenable quotients"
   (arXiv:1512.02135, l.261–262, quoted in
   `research/artifacts/solve-higman-sofic-2026-09-13.md`).
3. **(NAQ) is a question about simple groups.** (NAQ) is equivalent to:
   `Hig` has no quotient that is an infinite, finitely generated, simple,
   amenable group. Such a quotient `S` would contain four embedded copies of
   `BS(1,2)`, and its generators would have infinite order
   ([[nontrivial-higman-quotients-keep-all-four-bs-subgroups]]). It would be
   neither elementary amenable nor LEF
   ([[nontrivial-higman-quotients-are-not-locally-elementary-amenable]]).
4. **Contrapositive: a refutation lane.** Suppose `Hig` has a nontrivial
   amenable quotient, or more generally a nontrivial MF quotient. Then
   `(HMF5)` fails. Explicit finite-dimensional tuples then exist with relator
   defect tending to `0` and `||U_0 - 1||` bounded below.
5. **General form.** For every group `G`, `Rad_MF(G) = G` holds exactly when
   no nontrivial quotient of `G` is MF. So every candidate group for endpoint 6
   of [[property-t-free-manuscript-results]] must have no nontrivial amenable
   quotient.

## What this changes

- **The Higman route contains an open problem.** Every proof of `(HMF5)`
  answers the Helfgott--Juschenko question negatively. It must exclude
  infinite simple amenable quotients, such as the Juschenko--Monod topological
  full groups. It must also exclude every amenable quotient that is not
  elementary amenable. Neither exclusion is available anywhere in the
  repository:
  [[nontrivial-higman-quotients-are-not-locally-elementary-amenable]] stops at
  class `D`.

  So (NAQ) is a necessary prerequisite of `(HMF5)` that can fail on its own. It
  is purely group-theoretic and involves no operator norms. The wave-12
  decomposition `(HMF5) <=> (PUU) + (CGC)`, from
  `bs12-conjugator-correction-is-power-uniform-defect` (commit d5ba1ac4e6),
  therefore has the same cost. The two conditions together imply (NAQ). If
  `(PUU)` is ever established, `(CGC)` alone implies (NAQ).
- **What any proof of the collapse must contain.** A proof of `(HMF5)` must
  contain, explicitly or implicitly, an argument that excludes infinite simple
  amenable quotients of `Hig`. The known facts about `Hig` are not known to
  give such an argument. They are:
  - Higman's no-finite-quotient theorem;
  - the class-`D` exclusion;
  - infinite order of the generators and injectivity of the `BS(1,2)` edges;
  - torsion-freeness;
  - acylindrical hyperbolicity;
  - vanishing cohomological invariants.

  This is exactly why the Helfgott--Juschenko question is open. So a route to
  `(HMF5)` whose steps use only these facts, plus operator-norm estimates that
  hold equally well in amenable groups, cannot close. Somewhere a step must
  fail for every amenable group generated by four elements satisfying the
  Higman relations nontrivially. The recorded plateau of the Z/4 numerical
  census is consistent with either answer to (NAQ).
- **Two conjectures meet at the same question.** "`H4` has no nontrivial
  sofic quotient" (the non-sofic route, via
  [[base-two-exponential-permutations-iff-sofic-higman-quotient]]) and
  `(HMF5)` (the non-MF route) both imply (NAQ). A single infinite simple
  amenable quotient of `Hig` refutes both at once.
- **Endpoint 6.** The clause "all of whose nontrivial quotients again have full
  MF radical" costs nothing once `Rad_MF(G) = G`, because full-radical groups
  are closed under quotients
  ([[full-mf-radical-groups-form-an-extension-colimit-class]]). The real price
  of the endpoint is item 5: no nontrivial amenable quotient. For a simple
  nonamenable candidate this is automatic. For `Hig` it is the open question
  above.
