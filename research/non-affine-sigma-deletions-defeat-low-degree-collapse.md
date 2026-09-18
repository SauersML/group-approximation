---
rg: 2
id: non-affine-sigma-deletions-defeat-low-degree-collapse
kind: claim
title: Sparse non-affine corrections of Hadamard-view verifiers drop the value from that of the coarsening (one) to o(1) at completeness 1 - 2^(1-k), so affine views with arbitrary sigma collapse only to a label-deletion coarsening
distinct_from:
  low-degree-view-collapse-survives-non-affine-sigma: that is the proposed collapse for bounded-degree views with arbitrary bijections sigma; this refutes it already for identity views, and replaces the conclusion by the deletion coarsening Can_del.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that treats affine sigma, where acceptance above 1/p means exact acceptance; this treats arbitrary sigma over affine views, where acceptance above 1/p only rounds a triple to a bijection with a sparse deleted set, and shows the deleted set can carry the whole soundness.
  low-degree-view-unique-verifiers-collapse: that bounds the exact weight through the degree of sigma o rho_w - rho_(w'); this shows the degree bound cannot be traded for the degree of the views alone.
artifacts:
  - experiments/non-affine-sigma-deletions-2026-09-17/check_deletion_collapse.py
  - experiments/non-affine-sigma-deletions-2026-09-17/output.txt
---

**ESTABLISHED.** Use the model of `linear-view-unique-verifiers-collapse-to-quotient-coarsening`
(prime `p`, linear outer game `Phi` with affine constraint spaces `H_e`, owners
`o(w)`, views `rho_w : A_(o(w)) -> F_p^k`, triples `t = (w, w', sigma)` with
total weights `tau_t = mu_e tau_e(t)` summing to 1, oblivious completeness `c`), but let every `sigma` be an
**arbitrary** bijection of `F_p^k`. Write `a_t` for the fraction of `h in H_e`
accepted by honest labels on `t`.

**A. Counterexample (refutes `low-degree-view-collapse-survives-non-affine-sigma`).**
Let `p = 2`, `K = 2^k`, and fix any multigraph on `n` vertices with `m` edges.
Every vertex has label space `F_2^k`. Every edge `e = (a,b)` carries
`H_e = { (x, M_e x) }` with `M_e` uniform in `GL_k(F_2)` and a uniform `u_e != 0`,
all independent. Views are identities (degree `d = 1`). Put
`sigma_e = M_e` and `sigma'_e = M_e o swap(0, u_e)`.

- `V_pert` uses the triple `(a, b, sigma'_e)` on every edge. Its completeness is
  `1 - 2^(1-k)`. It has no exact triple. Rounding each triple to the bijection it
  agrees with on most of `H_e` gives `M_e`, and the rounded game is `Phi` read as a
  unique game. Its value is 1, attained by the labelling `x = 0`.
- `V_mix` uses `(a, b, sigma_e)` and `(a, b, sigma'_e)` with weight `1/2` each. Its
  completeness is `1 - 2^(-k)` and `w_ex = 1/2`.
  `Can_part(Phi, V_mix) = Can(Phi, V_mix)` is `Phi` read as a unique game, with value 1.

For every `s in (0,1]`, with `K_0(s) = 64 e^3 / s^3`, if `K >= K_0(s)` and `m >= 3n/s`, then
with probability at least `1 - 2K^(-n)`
```text
val(V_pert(Phi)) <= s        and        val(V_mix(Phi)) <= 1/2 + s.
```
So at `eps = 2^(1-k) -> 0` and `d = 1 <= (1 - gamma) log_2(1/eps)`, the inequality
`val(V) >= (1 - o(1)) val(Can_part) - o(1)` fails. It fails for `V_mix` with a
nonempty coarsening carrying half the weight, and for the rounded coarsening of
`V_pert`. Each non-exact triple deletes only the two labels `{0, u_e}` of `M_e`,
a `2^(1-k)` fraction. The first-moment bound holds for **every** fixed graph.

**B. What survives: the deletion coarsening.** Call `t` *roundable* if the views
of `t` have equal kernels on the direction space of `H_e`. Then `H_e` induces a
bijection `beta_t : A_a/K_w -> A_b/K_(w')` (as in the affine claim). Put
`D_t = { j : sigma(rho-bar_w(j)) = rho-bar_(w')(beta_t j) }`. Let `w_r` be the total
weight of roundable triples.

1. **Rounding threshold.** A non-roundable triple has `a_t <= 1/p`. Hence
   `w_r >= (pc - 1)/(p - 1)`. A roundable triple has `|D_t| = a_t |A_a/K_w|`, and
   ```text
   sum over roundable t of tau_t (1 - a_t)  <=  1 - c.
   ```
2. **Collapse.** Let `Can_rd(Phi, V)` be the unique game on the vertices `(z, K)`
   (labels `A_z/K`) whose edges are the roundable triples, with weights
   `tau_t / w_r` and constraints `beta_t`. Let `Can_del(Phi, V)` be the same game
   with each `beta_t` restricted to `D_t`: a labelling satisfies `t` only if the
   label `j` of the `w`-endpoint lies in `D_t` and the other label is `beta_t j`.
   For every input `Phi`,
   ```text
   val(V(Phi)) >= w_r * val(Can_del(Phi, V)).
   ```
   Branch blindness (item 5 of the affine claim) holds for roundable triples.
3. **Spread lemma.** Let `S` be the space of homogeneous symmetries, the tuples
   `s = (s_z)` of direction vectors with `(s_a, s_b)` in the direction space of
   `H_e` for every edge. `S` acts on labellings of `Can_rd`, `l -> l + [s]`, and
   preserves the value of `Can_rd`. For every labelling `l`,
   ```text
   E_(s in S) val(Can_del)(l + [s])  >=  val(Can_rd)(l) - sum_(t roundable) (tau_t / w_r)(1 - a_t) [L(A_a)/K_w : W_t],
   ```
   where `W_t` is the image of `s -> s_(o(w)) + K_w` in `L(A_(o(w)))/K_w`. If every `W_t`
   is everything, then `val(V(Phi)) >= w_r val(Can_rd(Phi,V)) - (1 - c)`, and arbitrary
   `sigma` gives nothing beyond affine `sigma`.
4. **The index is needed.** In A, if the graph is connected with at least two
   independent cycles, then `S = {0}` with probability at least `1 - 1/(K-1)`. Each
   index is then `2^k` and the bound in 3 is empty, as it must be.

**Consequence for `unique-games-conjecture`.** The coarsening obstruction for
Hadamard, Grassmann and subspace views is exact only when `sigma` is affine. With
arbitrary `sigma`, a verifier on top of a linear outer game still factors through a
test-free, branch-blind coarsening, but it is the **deletion coarsening**
`Can_del`: `Can` with at most a `(1 - c)/w_r` average fraction of labels removed from
the constraints. By A, those removals can carry all of the soundness. They do so by
killing labellings of `Can` that concentrate on a sparse, locally definable set of
labels, here the zero labelling. By 3, removals matter only when the outer game's
homogeneous symmetry space has large index in the view quotients. That holds for
folded, over-determined 3LIN inputs (only the zero symmetry). It fails for the
unfolded Grassmann agreement game, where every global linear function is a
symmetry. So `low-degree-view-collapse-survives-non-affine-sigma` is false. The
class-killing statement is established for affine `sigma`, and for arbitrary `sigma`
over outer games whose symmetries surject onto the views. The door left open is a
proof that `Can_del` of hard 2-to-2 families is sound, with deletions at density
`O(eps)` aimed at concentrated labellings.

This neither proves nor refutes UGC.

DERIVATION non-affine-sigma-deletions-defeat-low-degree-collapse-proof
