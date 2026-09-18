# Extension certificates carry no information about finiteness of cost

September 17, 2026. Worker `swarm-0917-w4-fp-nonamenably-gen` (card
inverter), cone `fpbs-fixed-price-universal`, target
`fpbs-fixed-price-non-amenably-generated-from-fg`.

Contents:
- §1 proves that the cost spectrum over the free extensions of a free
  action is flat (Theorem 1). The only import is the lifting inequality,
  which is recorded in Cairn.
- §2 derives the class kill (Corollary 2). A route that certifies a bound
  on the cost of an extension of `b`, and then descends to `b`, has
  exactly (U) as its descent step. The invariant is the cost of a free
  extension. The step where the route dies is descent along a factor map
  with non-atomic fibres.
- §3 checks the gate: finite fibres descend, and non-atomic fibres fail
  on every infinite-cost action.
- §4 applies this to `Gamma_mal` and its natural finitely generated
  overgroup, the ascending HNN extension `M`. It names both dead steps.

Status of this artifact:
- The lifting inequality is not new. It is recorded in [G00] Prop VI.21,
  as tabulated in `research/artifacts/fpbs/docs/fixed-price-countable-passage.md`,
  §2, and it is proved in
  `research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md`, (1.1).
- The product remark of §9 of the traffic document ("its product with the
  finite-cost action has finite cost and projects onto the infinite-cost
  one") is the special case `e = b x a_0` of Theorem 1(a).
- What is new here is the exact identity (1). It shows that inequality is
  the whole content of every extension route. Also new are the
  classification of which routes are extension routes, and the `M` analysis.

## 1. The flat extension spectrum

Conventions:
- `Gamma` is a countably infinite group.
- Actions are p.m.p. on standard probability spaces.
- An *extension* of a free action `b` is a free action `e` together with
  an equivariant measure-preserving factor map `e -> b`.
- `C(Gamma) = inf_a C(a)` over free `a`.

**Lifting inequality** ([G00] Prop VI.21, and traffic document (1.1)).
If `pi : e -> b` is a factor map between free actions, then
`C(e) <= C(b)`.
- Split a graphing of `b` into restrictions of group elements.
- Lift each piece `gamma|_D` to `gamma|_{pi^{-1}D}`. This has the same
  measure, because `pi` preserves the measure.
- A base path from `x` to `x g` uses letters whose product `w` satisfies
  `x w = x g`. By freeness of `b`, `w = g` almost everywhere. So the lifted
  path from `y` ends at `y g`, and the lifted graphing generates `E_e`.

**Theorem 1.** Let `b` be a free action of `Gamma`.

(a) Every extension of `b` has `C(e) <= C(b)`. If `C(Gamma) < infinity`,
then

    min { C(e) : e an extension of b } = C(Gamma),              (1)

and the minimum is attained by `e = b x a_0`, where `a_0` is any free
action with `C(a_0) = C(Gamma)`.

(b) Infinite cost descends to free factors: if `C(b) = infinity` and
`b -> c` is a factor map onto a free action `c`, then `C(c) = infinity`.
Finite cost ascends to free extensions.

*Proof.* (a) The inequality is the lifting inequality.
- A free `a_0` with `C(a_0) = C(Gamma)` exists by [G00] Prop VI.21
  ("C(Γ) is attained", passage document §2).
- `b x a_0` is free, since it has the free factor `b`. Both coordinate
  projections are factor maps.
- Lifting through the second projection gives
  `C(b x a_0) <= C(a_0) = C(Gamma)`.
- Every extension `e` is free, so `C(e) >= C(Gamma)` by definition.
- Hence the minimum in (1) is `C(Gamma)`, and it is attained at `b x a_0`.

(b) Lifting through `b -> c` gives `infinity = C(b) <= C(c)`. The second
sentence is the same inequality. ∎

**Corollary 1.** Suppose `C(Gamma) < infinity`. Then the following are
equivalent:
- (U) every free action of `Gamma` has finite cost;
- (D_prod) for all free `b`, `c`: `C(b x c) < infinity` implies
  `C(b) < infinity`;
- (D_ext) for every factor map `e -> b` of free actions:
  `C(e) < infinity` implies `C(b) < infinity`.

Proof:
- (U) implies (D_ext), trivially.
- (D_ext) implies (D_prod), by specialization.
- (D_prod) implies (U): given `b`, take `c = a_0` in Theorem 1(a).

Moreover, shape (B) of Theorem G in the passage document ("fixed pseudocost
plus a free action of infinite cost") holds if and only if some factor map
`e -> b` of free actions has `C(e) = C(Gamma) < infinity = C(b)`. In that
case, **every** infinite-cost `b` is the base of such a map, namely
`b x a_0 -> b`.

## 2. The class kill

Fix `Gamma` with `C(Gamma) < infinity`. An *extension route* to finite cost
has the following shape. From a free `b`, build a factor map `pi : e -> b`
of free actions with some property `P`. Certify `C(e) <= K`. Then conclude
`C(b) < infinity`.

**Corollary 2 (every extension route is (U) in disguise).** Suppose `P`
holds for the coordinate projection `b x a_0 -> b` for every free `b`,
where `a_0` is a free action of cost `C(Gamma)`. Then the descent step
"`P` and `C(e) <= K` imply `C(b) < infinity`", for any `K >= C(Gamma)`,
is equivalent to (U). If (U) fails, the step is false. If (U) holds, the
route proves nothing new.

*Proof.* If (U) fails, take `b` with `C(b) = infinity`. Theorem 1(a) gives
`C(b x a_0) = C(Gamma) <= K`, and `P` holds by assumption. So the
implication fails at `b`. If (U) holds, the conclusion is true for every
`b` whatever `P` says. ∎

The hypothesis on `P` is weak. The minimiser `a_0` can be chosen weakly
mixing (even mixing): replace `a_0` by `a_0 x s` with `s` a Bernoulli shift.
This is free, and lifting gives `C(a_0 x s) <= C(a_0)`. So `P` may include
any of the following, and Corollary 2 still applies:
- a direct product, or a relatively independent joining over `b`;
- non-atomic fibres;
- relative weak mixing, or relative mixing;
- "the fibre action has cost `C(Gamma)`";
- "`e` is the restriction of an action of an overgroup", when `a_0` itself
  is such a restriction.

**Routes this classifies as extension routes, and so kills as independent
mechanisms:**
1. *Products, joinings and noise.* Replace `b` by `b x c` or a joining, and
   bound the cost of that.
   - Theorem 1(a) makes the bound automatic.
   - In particular, extending the Bernoulli-noise identity
     `fpbs-bernoulli-noise-does-not-change-cost` (proved for finitely
     generated groups) to countable `Gamma` would prove only
     `C(b) = C(b x s) <= C(s)`. So it gives (U) only together with
     `C(s_Gamma) < infinity`, which is itself a case of (U).
2. *Coinduction through an overgroup.* Take `Gamma <= Lambda` with `Lambda`
   finitely generated. The hypothesis gives
   `C_Lambda(CInd_Gamma^Lambda b) = C(Lambda)`. Restricting to `Gamma`
   gives an extension of `b`, via the coordinate at the trivial coset.
   - The route needs two descents. The first is from `Lambda`-cost to
     `Gamma`-cost of the restriction. The second is (D_ext) from the
     restriction to `b`.
   - The second descent is (U) by Corollary 1.
   - The first fails even for finiteness when `Gamma` is normal with
     quotient `Z`, by §4(i).
3. *Measure-equivalence transfer.* Couple `Gamma` with a finitely generated
   `Lambda` through a coupling `Omega`. The transfer that keeps `b` in view
   takes the diagonal `Gamma`-action on the joint action built from `b` and
   a `Lambda`-action induced through `Omega`. This action projects onto `b`,
   so it is an extension of `b`, and any cost control for it stops at the
   same descent step. The one exception is a stable orbit equivalence of
   `b` itself, where the compression formula transports cost exactly. That
   is a certificate on `b`, not an extension route, and producing it is the
   problem.

**Invariant and dying step.**
- The invariant is the cost of a free extension. Over the extensions of a
  fixed `b` it is constantly equal to `C(Gamma)` at its minimum, so it
  cannot see `C(b)`.
- Every member dies at descent along a factor map with non-atomic fibres.
- Among positive mechanisms, only *base-measurable* certificates survive.
  These are graphings on `b` itself, the `J_pi = 0` regime of the traffic
  document §9.
- They include the chain condition of Proposition F and test case T5 of
  the passage document. The recorded finite-contact obstruction
  (`fpbs-malnormal-subgroup-relations-finite-contacts`) kills these for
  subgroup-anchored repair at `Gamma_mal`.
- Together, both known ways of certifying (U) are closed at `Gamma_mal`.
  What remains is base-measurable repair from subrelations that do not lie
  in any almost malnormal subgroup orbit relation.

## 3. The gate: which fibres descend

- **Finite fibres descend.** For a factor map of free actions with uniform
  `q`-point fibres,
  `research/artifacts/fpbs/docs/finite-fiber-cost-descent.md`, (1), gives
  `C(X) <= 1 + q(C(Y) - 1)`. So finiteness of cost descends, and (D_ext)
  holds for such maps with no hypothesis on `Gamma`.
  - The proof adds the fibre relation, which here is a finite relation of
    cost `(q-1)/q`. It then compresses to a fundamental domain.
- **Non-atomic fibres do not.**
  - An aperiodic countable relation inside the fibres costs at least `1`.
    Its union with `E_e` is a countable relation, but it is not the pull
    back of `E_b`, which has uncountable classes. So the compression step
    has no analogue.
  - Theorem 1(a) shows the failure is total. If (U) fails, then for every
    infinite-cost `b`, the non-atomic map `b x a_0 -> b` is a
    counterexample to descent.
- **Summary.** Descent of finiteness holds along bounded atomic fibres. It
  is equivalent to (U) along non-atomic fibres.

## 4. `Gamma_mal` and its ascending HNN overgroup

Setup:
- `Gamma_mal = lim (F_2 -> F_2 -> ...)` along `phi(a) = a`,
  `phi(b) = b a b^-2`.
- The shift is an automorphism `T` of the direct limit.
- `M = Gamma_mal ⋊_T Z` is the ascending HNN extension `F_2 *_phi`,
  generated by `a`, `b`, `t`. It is finitely generated.
- Under the hypothesis of the target claim, `M` has fixed price.

Route: from a free `b` of `Gamma_mal`, form `beta = CInd_{Gamma_mal}^M b`.
Since `M/Gamma_mal = Z`,

    beta|_{Gamma_mal}  ≅  (x)_{k in Z} (b o T^k)   on X^Z,

a product of twists of `b`. Each twist has the same orbit relation as `b`,
so the same cost. The hypothesis gives `C(beta) = C(M) < infinity`. Two
steps are needed.

(i) *From `C(E_beta^M) < infinity` to `C(E_beta^{Gamma_mal}) < infinity`.*
- This is descent to a normal subrelation with quotient `Z`, and finiteness
  fails there in general.
- Take `F_inf x Z`. It has fixed price 1 ([G00] Prop VI.23: "Γ_1 has an
  element of infinite order and Γ_2 is infinite ⇒ Γ_1 × Γ_2 has fixed price
  1", passage document §2).
- Every free action restricted to the normal subgroup `F_inf` is free and
  has cost infinity ([G00] Prop VI.9, "F_∞ ... fixed price ∞").
- So step (i) needs information specific to `M`.

(ii) *From the product of twists to `b`.*
- This is (D_ext) for the coordinate projection, which has non-atomic
  fibres.
- By Corollary 1 it is equivalent to (U) for `Gamma_mal`.
- No coordinate of the product has cost below `C(b)`. So lifting yields
  nothing even in principle.

So the natural finitely generated host of `Gamma_mal` gives no route to
(U) through coinduction. Even if step (i) were repaired, step (ii) is the
target itself.
- By Theorem G of the passage document and the recorded exclusion of shape
  (A) for locally free groups, fixed price for `Gamma_mal` is equivalent to
  (U) for `Gamma_mal`.
- Every free action of `Gamma_mal` has cost 2 or infinity.
- Hence the statement "some extension route certifies fixed price for
  `Gamma_mal`" is equivalent to fixed price for `Gamma_mal`.

## References

- [G00] D. Gaboriau, *Coût des relations d'équivalence et des groupes*,
  Invent. Math. 139 (2000). Propositions VI.9, VI.21, VI.23, quoted as
  tabulated in `research/artifacts/fpbs/docs/fixed-price-countable-passage.md`, §2.
- `research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md`, §1
  (lifting (1.1)) and §9 (mixed finite/infinite remark).
- `research/artifacts/fpbs/docs/finite-fiber-cost-descent.md`, §1.
