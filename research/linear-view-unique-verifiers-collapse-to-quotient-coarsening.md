---
rg: 2
id: linear-view-unique-verifiers-collapse-to-quotient-coarsening
kind: claim
title: Above completeness 1/p every affine-view unique verifier over a linear outer game is no sounder than a test-free quotient coarsening of the outer game, which for 2-to-2 inputs never reads a branch bit
distinct_from:
  derived-unique-game-lower-bounds-the-noise-test: that bounds the long-code noise test, whose views are nonlinear, and needs a matching decoder; this covers every verifier whose encodings are affine in the outer label (Hadamard, Grassmann and subspace encodings, the 2-to-2 machinery), needs no decoder, and yields an equivalence rather than a lower bound for one test.
  unique-constraints-orient-at-most-half-of-a-fiber: that is the exact injectivity wall for gadgets at perfect completeness; this is the quantitative version for arbitrary affine-view verifiers at any completeness c > 1/p, with the weight bound (pc-1)/(p-1) and the collapse theorem.
  unique-games-hard-at-completeness-one-half: that is the split reduction sitting at c = 1/2; this theorem is tight there, since the split has c = 1/2 and zero exact weight.
artifacts:
  - experiments/linear-view-collapse-2026-09-17/check_collapse.py
---

**ESTABLISHED.** Fix a prime `p`.

*Outer linear game `Phi`.* A weighted graph `(Z, E, mu)`. Each `z` has a label
space `A_z`, a finite affine space over `F_p`. Each edge `e = (a,b)` carries an
affine subspace `H_e <= A_a x A_b` whose projections onto `A_a` and `A_b` are
onto. Affine projection games qualify. So do linear 2-to-2 games, with
`H_e = { T x_a + T' x_b in b + <c> }` and `T, T'` invertible.

*Affine-view unique verifier `V`.* Output vertices `W` with owners
`o : W -> Z` and affine views `rho_w : A_(o(w)) -> F_p^k`. Each outer edge
`e = (a,b)` carries a distribution `tau_e` on triples `(w, w', sigma)` with
`o(w), o(w') in {a,b}` and `sigma` an affine bijection of `F_p^k`. The output
unique game `V(Phi)` has alphabet `F_p^k`: draw `e ~ mu`, then a triple from
`tau_e`, and accept iff `sigma(F(w)) = F(w')`. Honest labels are
`F(w) = rho_w(x_(o(w)))`.

*Oblivious completeness `c`.* Let `c_e` be the acceptance of honest labels,
averaged over a uniform `h in H_e` and over `tau_e`, and let `c = sum_e mu_e c_e`.
This is a property of the verifier on local constraints, not of `val(Phi)`.
So it holds on NO instances as well.

A triple is **exact** if honest labels satisfy it for *every* `h in H_e`. Let
`w_ex` be the total weight of exact triples.

1. **Rigidity threshold.** The set of `h in H_e` accepted by one triple is empty
   or an affine subspace. So every non-exact triple accepts at most a `1/p`
   fraction, and
   ```text
   w_ex >= (p c - 1) / (p - 1)          (= 2c - 1 for p = 2).
   ```
   With a non-affine bijection `sigma`, acceptance above `1/p` still forces equal
   view kernels on `H_e`.
2. **Exact triples are induced by `Phi`.** Let `K = ker rho_w` and
   `K' = ker rho_(w')`. On an exact triple, `H_e` induces a bijection
   `beta : A_(o(w))/K -> A_(o(w'))/K'`. It depends only on `H_e`, the owners
   and the kernels, not on `sigma` or the offsets. If `o(w) = o(w')`, then
   `K = K'` and `beta = id`.
3. **Collapse.** Let `Can(Phi, V)` be the unique game on vertices
   `(z, K)` with labels `A_z/K`, whose edges are the exact triples with
   constraints `beta` and their weights. Then, for **every** input `Phi`,
   ```text
   val(V(Phi)) >= w_ex * val(Can(Phi,V)) >= ((p c - 1)/(p - 1)) * val(Can(Phi,V)).
   ```
   If `x` satisfies outer weight `1 - eta`, then
   `val(Can) >= 1 - eta (p-1)/(pc-1)`.
4. **Equivalence.** Suppose a family of such verifiers with `c > 1/p` proves
   `Gap-UG(c_G, s)` NP-hard from `Gap-Phi(1-eta, s_Phi)`. Then the test-free map
   `Phi -> Can(Phi,V)`, computable in polynomial time by linear algebra, proves
   `Gap-UG(1 - eta (p-1)/(pc-1), s (p-1)/(pc-1))` NP-hard. Conversely, `Can` is
   itself an affine-view verifier with `c = 1`.
5. **Branch blindness for 2-to-2 inputs.** On an exact cross triple for
   `T x_a + T' x_b in b + <c>`, both branch directions are killed:
   `T^-1 c in K` and `T'^-1 c in K'`. So `Can` reads each 2-to-2 constraint
   only modulo its branch line, on quotients of alphabet size at most `p^(l-1)`.
   Its value is the same for both branch choices of every constraint.
6. **Tightness.** The split reduction behind
   `unique-games-hard-at-completeness-one-half` uses identity views with the two
   branch constraints. It has `c = 1/2` and `w_ex = 0`. So the threshold `1/p`
   in (1) cannot be lowered for `p = 2`.

**Consequence for `unique-games-conjecture`.** With affine encodings, the codim-1
agreement edges of the Grassmann test are what drive the 2-to-2 theorem's
soundness. Above completeness `1/2` they are non-exact, and they can be
deleted at the cost of the factor `w_ex`. Any proof of near-1 UG hardness
through affine-view encodings on top of a linear outer game is therefore
already a proof that the branch-blind quotient coarsening `Can` is hard. That
map has no encoding and no test, so no Grassmann expansion theorem can
contribute to it. In stability language, affine objects have no 99% regime:
agreement above `1/p` is exact agreement. A verifier that crosses the `1/2`
wall must use views that are not affine in the outer label, such as the long
code of Braverman--Khot--Minzer. Its analogue there is
`derived-unique-game-lower-bounds-the-noise-test`.

This neither proves nor refutes UGC. Whether branch-blind quotient coarsenings
of hard 2-to-2 instances are themselves hard is open, and by (4) that question
*is* the affine-view case of the problem.

DERIVATION linear-view-unique-verifiers-collapse-proof
