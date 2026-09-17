---
rg: 2
id: quantum-surjunctivity-conjecture
kind: claim
title: Over every group, every equivariant finite-propagation unital *-endomorphism of the quasi-local matrix algebra is onto
distinct_from:
  gottschalk-surjunctivity-conjecture: that is classical surjunctivity of full shifts; this is the operator-algebraic analogue for *-endomorphisms of the tensor product of M_d over G, where injectivity is automatic and strictness means not onto.
  injective-ca-pullbacks-extend-to-matrix-observables: that asks a specific classical encoder pullback to extend multiplicatively, which is equivalent to the goal; this quantifies over all quantum automata, with no classical input.
  sofic-groups-are-quantum-surjunctive: that proves this statement on sofic groups.
  clifford-quantum-surjunctivity-iff-stable-finiteness: that settles the Clifford sector of this statement, which is equivalent to Kaplansky stable finiteness over F_p.
  trace-preserving-endomorphism-fixes-discrete-type-i-summand: that is a von Neumann statement about discrete type I summands of the relative commutant; here, on infinite groups, the relative commutant of a strict automaton is a II_1 factor, so that node applies only to the trivial case.
artifacts:
  - experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2.py
  - experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2-output.txt
---

**OPEN.** Let `G` be a group and `d >= 2`, and write `A = (x)_G M_d` for the quasi-local C*-algebra with the shift
`alpha`. Every unital *-endomorphism `Phi` of `A` that satisfies both conditions below is onto:
- `Phi alpha_g = alpha_g Phi` for all `g`;
- `Phi(A_e) <= A_N` for some finite `N`.

`Phi` is automatically injective, because `A` is simple.

This is the quantum premise of `gottschalk-via-quantum-surjunctivity`. The transfer premise is
`strict-automata-yield-strict-quantum-endomorphisms`.

## Attempts

**2026-09-17 (a-gs-quantum, playbook lane (a)).**

- **Structure (established).** `quantum-endomorphisms-split-off-their-relative-commutant`.
  - `A = Phi(A) (x) D`, where `D = Phi(A)' n A`.
  - `Phi` is onto if and only if the local defect algebra `F <= D n A_(N^-1 N)` is `C`.
  - On infinite `G`, `[R : Phi(R)]` is `1` or `infinity`, and `Phi_* = id` on `K_0`.
- **Obstruction (class killed).** The invariant is the relative commutant. Every approach through index
  quantization, trace scaling or K-theory dies at the step "strictness gives a finite invariant greater than 1".
  - A strict `Phi` has infinite index, an infinite-dimensional simple monotracial commutant `D` with
    `A (x) D = A`, and acts trivially on `K_0(A) = Z[1/d]`.
  - Playbook item "the index can only take Jones' values" is vacuous: only `1` and `infinity` occur.
- **Wiring automata (step 1).** Consider `Phi(A_(g,i)) = A_(g s_i, pi(i))`, with several `M_p` per site. It is a
  unital *-homomorphism only if the target sites are distinct, so `pi` is a bijection of `[n]`. Then the site map
  is a bijection of `G x [n]`, and `Phi` is an automorphism.
  - There is no compression on any group. This is folded in here rather than made a node, because it is the
    trivial case of the defect criterion (`F = C`).
- **Amenable and sofic groups (step 2, established).** `sofic-groups-are-quantum-surjunctive`.
  - Translates of the defect `F` are packed into the relative commutant of the transplanted rule on a sofic model.
  - Connes-Stormer entropy is not needed.
- **Computer search on `F_2 = <a,b>`, `d = 2`, `N = {1, a, b}` (step 3).**
  - A strict solution cannot exist, because `F_2` is sofic.
  - The Clifford sector was enumerated for `p = 2, 3, 5` by
    `experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2.py`. All `3 |Sp_2(F_p)|` solutions are wirings
    composed with on-site gates.
  - Beyond Clifford, every overlap `hN n N` is one site. The support algebras of `Phi(M_d)` on the three slots then
    pairwise commute. For prime `d` this appears to force a single slot to carry all of `M_d`, but that analytic
    classification is recorded only as a remark; the sofic theorem makes it unnecessary.
  - **Pivot.** The search lane is closed on `F_2`. Only non-sofic groups can carry a counterexample.
- **Clifford sector (established).** `clifford-quantum-surjunctivity-iff-stable-finiteness`.
  - A Clifford automaton is a matrix `M` over `F_p[G]` with `M J M^* = J`. It is onto if and only if `M` is a unit.
  - Hence this conjecture implies Kaplansky stable finiteness over every `F_p`. It is not easier than the classical
    conjecture on that axis.
  - A counterexample search on non-sofic hosts should start outside the Clifford sector, since Clifford
    counterexamples are exactly Kaplansky failures.
- **One dimension (imported).** Schumacher-Werner, "Reversible quantum cellular automata", quant-ph/0405174:
  - "A further bonus from our proof of the structure theorem is that it does not actually require the global rule
    to be an automorphism: it works under the prima facie much weaker assumption that the global rule is a
    homomorphism (and not necessarily onto). Then invertibility follows (see Corollary~\ref{cor:invert} below)."
  - "The inverse of a nearest neighbor QCA exists, and is a nearest neighbor QCA."
  - This is the `G = Z` case. Their support-commutation step uses the linear order of `Z` and fails for more than
    one generator, which is why the sofic count is needed.
- **Where it stops.** On non-sofic groups with all `F_p[G]` stably finite, no tool is known.
  - The count in `sofic-groups-are-quantum-surjunctive-proof` needs a finite model with a near-bijective transplant
    of the local rule. Its Step 1 uses multiplicativity of the model on `(N u N^-1)^8`.
  - A hyperlinear model (unitaries in place of permutations) does not transplant the rule. The rule is a
    *-homomorphism on a tensor product indexed by points, and approximate unitary models have no points.
  - So the hyperlinear extension of the count dies at Step 1.
