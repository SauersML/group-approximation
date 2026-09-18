---
rg: 2
id: orderable-nonsofic-iff-order-realizable-forbidden-table-proof
kind: route
title: Compactness for order clauses and openness of nonsoficity reduce the orderable nonsofic cells to finite tables
target: orderable-nonsofic-iff-order-realizable-forbidden-table
requires: []
---

Notation as in [[orderable-nonsofic-iff-order-realizable-forbidden-table]].  `P` is LO, BO or LI.

**Step 0: soficity by tables.**  A group `G` is sofic iff every finite table of `G` has an `eps`-model for every
`eps > 0`.  Here a *table of `G`* is a finite `F <= G` with `m(x,y) = xy` whenever `xy in F`.  This is the standard
definition (Pestov, Bull. Symb. Logic 14 (2008), with the separation condition in the form
`d(sigma(x), sigma(y)) >= 1 - eps`).  The form "`sigma(x)` has at most `eps n` fixed points for `x != 1`" is
equivalent: apply the other form to `F u F^-1 F` and use `sigma(x^-1) sigma(y) ~ sigma(x^-1 y)`, at the cost of a
constant factor in `eps`.

- (S1) *Nonsofic groups carry forbidden tables.*  If `G` is not sofic, some table of `G` is forbidden at some `eps`.
- (S2) *Forbidden tables force nonsoficity upward.*  Let `T` embed in `H` by `f`.  Then `f(F)` with the products of
  `H` that land in `f(F)` is a table of `H`, and it defines every product `m` defines.  An `eps`-model of that table,
  composed with `f`, is an `eps`-model of `T`.  So if `T` is forbidden, `H` is not sofic.

**Step 1: largest `P`-quotients.**  Each `P` is closed under subgroups and under arbitrary direct products.
- LO and BO: well-order the index set and compare two distinct tuples at the first coordinate where they differ.
  Left multiplication, and for BO right multiplication too, does not change that coordinate or the comparison.
- LI: a nontrivial finitely generated subgroup `A` of a product projects nontrivially to some factor.  The image is
  a nontrivial finitely generated subgroup of an LI group, so it maps onto `Z`, and so does `A`.

Hence for any group `G`, with `N_P = intersection of all normal N with G/N in P`, the group `G/N_P` embeds in the
product of those quotients and has `P`.  It is the largest `P`-quotient `P(G)`.

**Step 2: order clauses.**  Let `Phi` be the free group on `F`.  Take propositional atoms `n_w` ("`w` is in the
kernel") and `p_w` ("`w >= 1`") for `w in Phi`.  Let `Theta_P(T)` consist of:

- (N) `n_1`; `n_u -> n_(u^-1)`; `n_u and n_v -> n_(uv)`; `n_u -> n_(g u g^-1)`, for all `u, v, g in Phi`;
- (R) `n_(x y m(x,y)^-1)` for every defined product;
- (O) `p_w or p_(w^-1)`; `p_u and p_v -> p_(uv)`; `(p_w and p_(w^-1)) <-> n_w`;
- (BO only) `p_u -> p_(g u g^-1)`;
- (LI only) `p_u and p_v -> p_(u^-1 v u^2)`;
- (D) `not n_(x^-1 y)` for `x != y` in `F`.

Let `Theta'_P(T)` be `Theta_P(T)` without (D).

*Claim A.  `Theta_P(T)` is satisfiable iff `T` embeds in a group with `P`.*

(<=) Let `f : F -> H` be an embedding, `H` in `P` with a suitable order (for LI, a Conradian left order:
Rhemtulla--Rolfsen and Brodskii, LI iff some left order is Conradian, and a left order is Conradian iff
`f, g > 1` implies `f^-1 g f^2 > 1`, Jiménez--Navas).  Extend `f` to `phi : Phi -> H` and put `n_w` true iff
`phi(w) = 1`, `p_w` true iff `phi(w) >= 1`.  (N), (O) and the BO clause are immediate.  (R) holds because `f`
respects `m`, and (D) holds because `f` is injective.  For the LI clause: if `phi(u)` or `phi(v)` is `1`, the
conclusion is `phi(v) >= 1` or `phi(u)^2 >= 1`.  Otherwise both are `> 1`, and the Conradian inequality applies.

(=>) Given an assignment, `N = {w : n_w}` is a normal subgroup of `Phi` by (N), containing the relators by (R).
`Pos = {w : p_w}` satisfies `Pos Pos <= Pos`, `Pos u Pos^-1 = Phi` and `Pos n Pos^-1 = N`, by (O).  So
`Pos N <= Pos` and `N Pos <= Pos`, and `Pos/N` is the positive cone of a left order on `Phi/N` (`gN <= hN` iff
`g^-1 h in Pos`).  With the BO clause the order is bi-invariant.  With the LI clause it is Conradian: for `f, g > 1`
we get `f^-1 g f^2 >= 1`, and equality would give `g = f^-1 < 1`.  So `Phi/N` has `P`.  The relators give a
homomorphism `P_T -> Phi/N` respecting `m`, and (D) makes `F -> Phi/N` injective.

*Claim B.  For `w in Phi`, `w in N_P(P_T)` iff `Theta'_P(T) + {not n_w}` is unsatisfiable.*
The same two constructions, with (D) replaced by the single clause `not n_w`, show that this theory is satisfiable
iff some `P`-quotient of `P_T` does not kill `w`.

**Step 3: compactness.**  `Theta_P(T)` is a recursively enumerable set of finite clauses in countably many atoms.
By the compactness theorem of propositional logic, it is unsatisfiable iff some finite subset is.  Each finite
subset mentions finitely many atoms, so its satisfiability is decidable by truth tables.  So unsatisfiability of
`Theta_P(T)`, and likewise of `Theta'_P(T) + {not n_w}`, is `Sigma^0_1`, uniformly in `T` and `w`.

**Proof of the theorem.**
1. If `G` has `P` and is not sofic, (S1) gives a forbidden table of `G`, which embeds in `G`.  Conversely, (S2).
2. Suppose the forbidden `T` embeds in `H` with `P`.  The induced map `P_T -> H` has image in `P` (subgroup of `H`),
   so its kernel contains `N_P(P_T)`.  So the composite `F -> P(P_T) -> H` equals `f`, and the first map is injective
   and respects `m`.  By (S2), `P(P_T)` is nonsofic, and so is `H`.  `P(P_T)` is generated by `F`.  Its relators
   `N_P(P_T)` form an r.e. set by Claim B and Step 3, so it is recursively presented (Craig's trick).  A group with
   `P` generated by an embedded copy of `F` is a quotient of `P_T` with `P`, hence a quotient of `P(P_T)`.
3. By Claim A and Step 3, "`T` embeds in a group with `P`" is `Pi^0_1`.  "`T` is forbidden at `eps`" says: for every
   `n`, none of the finitely many maps `F -> Sym(n)` is an `eps`-model.  That is `Pi^0_1` for rational `eps`, and
   restricting to rational `eps` loses nothing.  By part 1 the existence sentence is
   `exists (T, eps) [forbidden and embeds]`, which is `Sigma^0_2`.
4. A nonsofic countable left-orderable group has a finitely generated nonsofic subgroup (soficity is local), which
   is countable and left-orderable.  Darbinyan--Steenbock embed it in a finitely generated simple left-orderable
   group, which is nonsofic because soficity passes to subgroups.  The converse is trivial.  ∎

**Checks on the method.**
- *LI is really propositional.*  LI is not visibly first-order (it quantifies over finitely generated subgroups and
  homomorphisms to `Z`).  The clause set sees it only through Conradian orders.  Direction (<=) uses only that an LI
  group has a Conradian left order, and (=>) only the Jiménez--Navas inequality, so no stronger or weaker property
  is being axiomatized.
- *A torsion-free non-LO group is refuted.*  The Promislow group is torsion-free and not LO.  If every finite table
  of it embedded in an LO group, it would embed in an ultraproduct of LO groups, which is LO (order coordinatewise
  modulo the ultrafilter).  So by Claim A and compactness some finite table of it has a finite clause refutation.  The torsion clause set does not apply to it,
  so the refutation must use the (O) clauses on several elements at once, as the Conrad--Ohnishi sign-choice
  criterion predicts.
- *Normality is needed in (N).*  A left preorder alone has a point stabilizer as its indifference set, which need
  not be normal, and then `Phi/N` is not a group.  The separate atoms `n_w` with the conjugation clause avoid this.
