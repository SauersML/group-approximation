---
rg: 2
id: one-sided-inverse-pairs-transfer-to-table-realizations
kind: claim
title: A one-sided inverse pair transfers to every realization of its product tables that separates the reversed products
distinct_from:
  strict-pairs-transfer-to-table-realizations: that transfers a strict automaton pair along realizations of memory and decoder tables and needs separation only on the orphan window; this transfers a group-algebra one-sided inverse pair along realizations of the two product tables A x B and B x A and needs separation on the reversed products BA u {1}.
  subgroup-supported-one-sided-inverse-rigidity: that excludes supports lying inside a subgroup whose group algebra is directly finite; this excludes support windows whose product tables realize in a finite group, with no subgroup inclusion and with collisions allowed off BA u {1}.
  kaplansky-direct-stable-finiteness-one-universal-group: that reduces all groups to one fixed finitely presented host through colimits of whole presentations; this attaches to each support window its own finitely presented table group and turns finite images of it into exact, rule-free exclusions.
---

**ESTABLISHED** by `one-sided-pair-table-realization-proof`. No novelty is
claimed. This is the finite-table form of the local argument behind the sofic
case of Kaplansky's direct finiteness conjecture (Elek–Szabó). It is recorded so
that searches can use it as an exact filter.

**Setting.**
- `k` is a field, `G` a group, and `A, B` finite subsets of `G`.
- `alpha = sum_(a in A) x_a [a]` and `beta = sum_(b in B) y_b [b]` in `k[G]`
  satisfy `alpha beta = 1 != beta alpha`.
- `C = A u B u AB u BA u {1}` is the set of cells.

**Theorem.** Let `H` be a group and `phi : C -> H` a map with `phi(1) = 1` and

    phi(a) phi(b) = phi(ab),     phi(b) phi(a) = phi(ba)        (a in A, b in B).

Push coefficients forward along `phi`. Then `phi_* alpha . phi_* beta = 1` in
`k[H]`, and `phi_* beta . phi_* alpha - 1 = phi_*(beta alpha - 1)`. If `phi` is
injective on `BA u {1}`, the pair `(phi_* alpha, phi_* beta)` is a strict
one-sided inverse pair over `H`.

**Corollaries.**
1. **Screen.** Suppose `k[H]` is directly finite, for instance because `H` is
   finite. Write `beta alpha - 1 = sum_g c_g [g]`. Then every fibre `F` of `phi`
   on `BA u {1}` has `sum_(g in F) c_g = 0`. Several realizations into finite
   groups combine into one realization into their product. So no strict pair is
   supported in `(A, B)` once the realizations found are jointly injective on
   `BA u {1}`. Otherwise the defect is confined to the classes of cells that all
   of them merge, with coefficient sum zero on each class.
2. **Table group.** Let `U(A, B)` be the group with generators `x_g` (`g in C`)
   and relators `x_1`, `x_a x_b x_(ab)^(-1)` and `x_b x_a x_(ba)^(-1)`. The map
   `g -> x_g` is a realization. It is injective on `C`, because composing it with
   the homomorphism `U(A, B) -> G`, `x_g -> g`, gives the inclusion. So a strict
   pair supported in `(A, B)` exists over `G` if and only if one exists over the
   finitely presented group `U(A, B)` on the canonical cells. When one exists,
   every finite image of `U(A, B)` merges two cells of `BA u {1}`.
3. **Balls.** Let `X` be a finite subset of `G` and `B_r` the ball of radius
   `r >= 1` in the word metric of `X u X^(-1)`. For `A = B = B_r`, `U(A, B)` is
   isomorphic to

       G_(4r) = < X | all words of length at most 4r in X u X^(-1) that are trivial in G >,

   with `x_g` sent to any word of length at most `2r` representing `g`. So
   supports in `(B_r, B_r)` carry a strict pair only if no homomorphism from
   `G_(4r)` to a finite group is injective on `B_(2r)`. If `<X>` has a
   presentation on `X` whose relators have length at most `4r`, then
   `G_(4r) = <X>`. At such radii finite images certify nothing beyond what
   `<X>` itself allows.

**Scope.** An exclusion from Corollary 1 is an exact certificate: the finite
images can be replayed against the relators of `U(A, B)`. It removes only the
windows it names. Corollary 3 bounds its reach on ball windows. For a finitely
presented `<X>` it becomes blind once `4r` reaches the relator lengths.
