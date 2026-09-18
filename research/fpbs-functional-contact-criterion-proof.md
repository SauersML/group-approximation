---
rg: 2
id: fpbs-functional-contact-criterion-proof
kind: route
title: One out-edge per point costs at most one, infinite contacts repair for free, and monotonicity moves the bound to Bernoulli and then to every free action
target: fpbs-functional-contact-criterion
requires:
  - fpbs-infinite-contact-zero-relative-cost
  - cost-is-constant-on-weak-equivalence-classes
  - fpbs-bernoulli-maximal-cost
---

Notation is that of the target. Let `a ≺ b_Gamma` be free on `(X,mu)` and let `f` be contact-connected.

## 1. The functional graphing has cost at most one

1. Write `D = {x : f(x) != x}`. By Lusin--Novikov, `R_a` is a countable union of graphs of Borel partial injections
   `phi_1, phi_2, ...` of `X`. So `D` splits into Borel pieces `D_i = {x in D : f(x) = phi_i(x), and f(x) != phi_j(x)
   for j < i}`, and `f` restricted to `D_i` is a partial injection.
2. The partial injections `f|D_i` form a graphing that generates `S_f` and whose unoriented edge set is `F_f`. Its
   cost is `sum_i mu(D_i) = mu(D) <= 1`.
3. If the graphing is not simple, drop duplicate unoriented edges. The cost does not increase, and the generated
   relation stays the same. Hence `c(F_f) <= 1`.

## 2. Zero relative repair cost

1. `H_a` is a simple generating graphing of `R_a` of finite cost `|S|/2`, because `S` generates `Gamma`, `e` is not
   in `S`, and `a` is free.
2. `S_f` is a Borel subrelation of `R_a`, and by hypothesis its contact graph is connected in almost every orbit.
3. `fpbs-infinite-contact-zero-relative-cost` then gives `C(R_a) <= c(F_f) <= 1`.
4. `Gamma` is infinite and `a` is free, so `C(R_a) >= 1` (`fpbs-bernoulli-maximal-cost`). Hence `C(a) = 1`.

The contact hypothesis already excludes finite components. A finite class meets only finitely many `H_a`-edges, so it
would be isolated in the contact graph. It is not the whole orbit, because the orbit is infinite.

## 3. Transfer to Bernoulli and to every free action

1. Monotonicity (`cost-is-constant-on-weak-equivalence-classes`: `b ≺ a` implies `C(a) <= C(b)`), applied to
   `a ≺ b_Gamma`, gives `C(b_Gamma) <= C(a) = 1`.
2. `fpbs-bernoulli-maximal-cost` says the supremum of costs of free actions of `Gamma` is attained by a nontrivial
   Bernoulli action.
3. All nontrivial Bernoulli actions of `Gamma` are weakly equivalent, and `b_Gamma` is weakly contained in every free
   action (Abért--Weiss, quoted in `cost-is-constant-on-weak-equivalence-classes`). So by monotonicity they have cost
   `C(b_Gamma)`, and this supremum equals `C(b_Gamma) <= 1`.
4. Every free action has cost at least one. So every free action has cost exactly one, which is fixed price one.

## 4. The tree remark in the target

Suppose the Cayley graph is a tree and `f` moves each point of `D` to a Cayley neighbour.
1. Then each component is connected in the tree, so it is a subtree.
2. Two disjoint subtrees joined by two distinct edges would give a cycle. So the contact graph has no edges.
3. The tree has degree `2r >= 4`. If an orbit were a single class, then `F_f` would contain every Cayley edge of that
   orbit, so its cost would be `r > 1`, contradicting §1. Hence orbits have several classes, the contact graph is
   disconnected, and `f` is not contact-connected.

For general `f`, the obstruction is the contrapositive of the theorem.
