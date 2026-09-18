---
rg: 2
id: thompson-f-invariant-pivot-orders-cannot-certify-doubling
kind: claim
title: "Biography of a non-amenability witness for F: two private points force a two-sided descent, so no one-sided invariant order is a pivot certificate for any set, and an order that first compares a bi-ordered quotient reduces the witness to one fiber of that quotient"
distinct_from:
  thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs: that is the sufficient condition (two private points at every m give doubling and non-Ore pairs); this gives necessary properties of any order that satisfies it, and kills every one-sided invariant order and reduces every order refining a bi-ordered quotient.
  thompson-f-ore-obstructions-must-see-finite-support: that rules out leading-term Ore obstructions for one bi-order; this is about the doubling side, for every left- or right-invariant total order on F and every finite set, including non-homogeneous ones.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills finite-state tree-automaton flows by averaging; this kills a different certificate class (pivot orders) with a pointwise antisymmetry argument at one deep element, and needs no averaging.
  three-element-doubling-sets-are-free-bases: that bounds the size of a doubling set from below using free subgroups; this constrains the certificates of a doubling set, and uses that bound only to size the reduced fiber.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that reduces non-amenability to doubling of Guba sets; this records which shapes of certificate for that doubling can exist.
artifacts:
  - experiments/thompson-f-witness-biography-2026-09-17/pivot_descent.py
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13.md
---

**ESTABLISHED** through `thompson-f-invariant-pivot-orders-cannot-certify-doubling-proof`
(direct proof; not independently reviewed; no priority claimed).

**Setting.** `M` is the positive monoid of `F`, and multiplication in `F` is the group operation.
Let `≺` be a total order.
- *Monoid form* (as in `thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs`).
  - `≺` is on `M`, and `S ⊆ M` is finite.
  - `w ∈ M` is *private for* `m` if `w ∈ S m` and `m` is the `≺`-maximum of `{m' ∈ M : w ∈ S m'}`.
  - A *pivot order for `S`* gives every `m ∈ M` at least two private points.
- *Group form.*
  - `≺` is on `F`, and `U ⊆ F` is finite.
  - `w` is private for `m` if `w ∈ U m` and `m` is the `≺`-maximum of `U^-1 w`.
  - A *group pivot order for `U`* gives every `m ∈ F` at least two private points. The same
    disjointness argument shows that `U` then doubles in `F`.
- *Deep elements.* The *deep set* of `S` is `R(S) = {m ∈ M : s'^-1 s m ∈ M for all s, s' ∈ S}`.

1. **Two-sided descent.**
   - *Group form.* If `t_1 m ≠ t_2 m` are private for `m`, then `g = t_2^-1 t_1 ≠ 1` satisfies
     `g m ≺ m` and `g^-1 m ≺ m`.
   - *Monoid form.* The same holds for `g = s_2^-1 s_1` at every deep `m ∈ R(S)`.
2. **Deep elements are cofinal.**
   - `R(S)` is a nonempty right ideal of `M`.
   - For every finite `Y ⊆ M` there is `r ∈ M` with `Y r ⊆ R(S)`.
   - For `m ∈ R(S)`, the factor set `{m' : s m ∈ S m'}` is `{s'^-1 s m : s' ∈ S}`, with `|S|`
     distinct elements.
3. **Invariant orders die.** Let `≺` be a left-invariant or a right-invariant total order on `F`
   (bi-invariant orders included).
   - *Group form.* For every finite `U` and every `m ∈ F`, `m` has exactly one private point: `t m`
     with `t m` the `≺`-minimum of `U m` in the left-invariant case, or `t` the maximum of `U` under
     `a ≺' b ⇔ a^-1 ≺ b^-1` in the right-invariant case.
   - *Monoid form.* The restriction of `≺` to `M` gives every `m ∈ M` at least one private point
     for every finite `S ⊆ M`, and every deep `m ∈ R(S)` exactly one.
   - Hence no one-sided invariant order on `F`, restricted to `M`, is a pivot order for any finite
     `S ⊆ M`. None is a group pivot order for any finite `U ⊆ F`.
   - *Where it dies.* At any deep element `m* ∈ R(S)` (group form: at any `m*`), two would-be private points
     give `m*^-1 g m* ≺ 1` and `m*^-1 g^-1 m* ≺ 1` (left-invariant), or `g ≺ 1` and `g^-1 ≺ 1`
     (right-invariant). The invariant killed is antisymmetry of the positive cone.
4. **Orders that first compare a bi-ordered quotient.** Let `λ : F → Γ` be a homomorphism and `<_Γ`
   a right-invariant total order on `Γ`, and let `≺` refine it: `λ(a) <_Γ λ(b) ⇒ a ≺ b`. Put
   `a ≤' b ⇔ a^-1 ≤_Γ b^-1` (a left-invariant order), and let `U_λ` be the set of `t ∈ U` at which
   `λ(t)` is `≤'`-maximal on `λ(U)`.
   - Every private point of every `m` (group form), or of every deep `m` (monoid form), is `t m`
     with `t ∈ U_λ`.
   - `U_λ` does not depend on `m`.
   - If `≺` is a group pivot order for `U`, then `U_λ` doubles in `F`.
   - If `≺` is a pivot order for `S ⊆ M`, then `S_λ` doubles in `M`.
   - In both cases `|U_λ| >= 4`, by `three-element-doubling-sets-are-free-bases` (item 2) and
     `thompson-f-has-no-free-subgroups`.
   - *Examples.* For `λ = id` with a bi-order, `U_λ` is a single point, which is item 3 again. For
     the abelianization `F → Z²` with any bi-invariant order on `Z²`, `S_λ` is one fiber. For
     homogeneous `S`, that means the monomials with an extreme number of letters `x_0` in normal
     form.
5. **Necessary structure of a witness** (combining established claims).
   - If `S_(m+1,m+d+1)` (or any finite `S ⊆ M`) doubles:
     - `|S| >= 4`;
     - every homogeneous doubling `S` has degree `>= 2`, since a degree-1 set lies in `X_m`,
       which the survey shows is not doubling;
     - the subgroup `H` generated by `s_0^-1 S` is a finitely generated non-amenable subgroup of
       `F`, and it carries the infinite nested descent of non-EA germ-trivial kernels of
       `plo-i-group-is-ea-iff-its-orbital-germ-kernels-are`, item 5.
   - Any pivot order certifying the doubling:
     - gives every deep `m` a two-sided descent `g ∈ S^-1 S \ {1}`;
     - is not one-sided invariant on the deep set;
     - if it refines a bi-ordered quotient `λ`, it certifies the smaller fiber `S_λ` instead.

**What survives, and a construction recipe.** A pivot certificate for a Guba set must be a
non-invariant order in which every deep `m` is a two-sided local maximum along some
`g ∈ S^-1 S \ {1}`. If it first compares a bi-ordered quotient that splits `S`, it is really a
certificate for the fiber `S_λ`, which must itself double.

The first falsifiable step toward a certificate for `P_(2,2)` is an explicit order on `M` with a
two-sided descent at every deep `m` of `R(S_(3,5))`. The seed `m*` has 21 leaves in
`experiments/thompson-f-witness-biography-2026-09-17/pivot_descent.py`.

Computed only (not part of the ESTABLISHED statement; `pivot_descent.py`, exact PL arithmetic, seed
20260917):
- *Invariant orders.* On 40 random `m ∈ F` and 25 deep `m ∈ M`, for `S_(2,4)` and `S_(3,5)`,
  exactly one private point under the germ-at-0 bi-order, a dynamical left order and its
  right-invariant mirror. This matches item 3.
- *Caret-count orders.*
  - Let `T_m` be the set of `t` for which `m` has an extreme caret count among `U^-1 t m`. An order
    that first compares caret counts needs `|T_m| >= 2`.
  - At the 25 sampled deep monoid elements, `m` has the most carets among the factors of every
    `s m`. So "more carets greater" leaves all `|S|` candidates, and "fewer carets greater" leaves
    at least 3 (for `S_(2,4)`) and at least 4 (for `S_(3,5)`). Neither is excluded on the deep set.
  - In group form, "more carets greater" gives `|T_m| <= 1` at 95% or more of the 40 sampled `m`.
    "Fewer carets greater" gives `|T_m| = 1` at some sampled `m`. So neither is a group pivot order
    for these sets.

**Scope.**
- The group-form parts of items 1, 3 and 4 hold in any group. The monoid-form parts use only that
  `M` is cancellative with common right multiples (Step 0 of
  `thompson-f-nonamenable-iff-some-monomial-set-doubles-proof`). The bound `|U_λ| >= 4` and item 5
  are specific to `F`.
- Item 3 is not a theorem about all orders on `M`. Pivot orders built from word length, caret
  counts with non-invariant tie-breaks, or tree shapes are not covered, except through item 4 when
  they refine a bi-ordered quotient.
- Nothing here bears on doubling certificates that are not orders, such as Hall matchings or flows.

Proof route: `thompson-f-invariant-pivot-orders-cannot-certify-doubling-proof`.
