# Strategist (negative side): untried counterexample routes, screened and ranked

Lane `w3-strategist-neg`, 2026-09-12. The job was to find the most decisive counterexample route that nobody
has tried. Section 1 records the candidates that die on arrival or turn out to be existing targets under a
new name, so nobody re-derives them. The later sections give the plans that survive the screen, ranked.

## 1. Screened candidates

### 1.1 Alphabet-increasing embeddings are impossible

Suppose |B| > |A| and there is an injective automaton `B^G -> A^G`. Composing it with the inclusion
`A^G -> B^G` would give a strict automaton on `B^G`. But no such automaton exists, for any group `G`.
- The fixed points of the shift action on `A^G` are exactly the constant configurations. `G` acts
  transitively on itself, so a fixed configuration takes one value everywhere.
- An equivariant map sends fixed points to fixed points, and an injective one does so injectively.
- So `|B| <= |A|`.

This is the embedding form of `full-shifts-with-different-alphabets-are-not-conjugate`. No route exists here.

### 1.2 Copy and pullback transfers are routing

- The bicyclic monoid `<p, q | qp = 1>` carries the injective, non-surjective automaton
  `tau(x)(m) = x(mq)`, because `m -> mq` is onto but not injective.
- Nonunimodular Hecke pairs `(G, H)` carry the analogous pullback along `gH -> gkH`, when `k^-1 H k` has
  index 2 in `H`.
- The end-fixing tree carries the parent copy `tau(x)(v) = x(p(v))`.

All three move symbols without computing with them.
- Over a group acting on itself, every equivariant map of the index set is a bijection `g -> gm`, as the
  calibration in `end-fixing-tree-symmetries-carry-strict-automata` notes.
- A transferred rule that still reads one symbol per output site falls under the routing screen
  `certificate-controlled-routing-is-surjunctive`. That scope is to be checked against that node's
  hypotheses; this section records a screen, not a theorem.

A monoid-to-group or Schreier-to-group induction must add arithmetic mixing. That puts it back in the
linear families or the nonlinear balance families. No new route.

### 1.3 Homomorphic automata over solvable group alphabets reduce to stable finiteness

**Claim** `homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness`. Let `K` be a finite solvable group
and `G` any group.
- If `F_p[G]` is stably finite for every prime `p` dividing `|K|`, then every injective automaton
  `K^G -> K^G` that is a group homomorphism is surjective.
- Conversely, a non-directly-finite `M_n(F_p[G])` gives a strict homomorphic automaton on `(F_p^n)^G`.

**Proof.**
1. **The local rule is a homomorphism.** It is `mu(x|_S) = tau(x)(1)`, and `tau` is a homomorphism, so
   `mu : K^S -> K` is one.
2. **Characteristic subgroups are preserved.** `[K^S, K^S] = [K,K]^S`, so `mu` maps `(K^(i))^S` into
   `K^(i)` for every term of the derived series. The same holds for the p-primary components and the
   subgroups `p^j L` of an abelian layer `L`. So `tau` preserves the filtration
   `K^G >= (K')^G >= ...`, refined until every layer is an `F_p`-vector space, and it induces homomorphic
   automata on the layers.
3. **The induction step.** Take a normal characteristic subgroup `N` with quotient `Q = K/N`, and suppose
   `tau` is injective.
   - `tau_N` is injective. By induction it is surjective.
   - If `tau(x)` lies in `N^G`, write `tau(x) = tau(n)` with `n` in `N^G`. Injectivity gives `x = n`, so
     `tau_Q` is injective. By induction it is surjective.
   - Given `y`, choose `x` with `tau_Q(xbar) = ybar`. Then `y = tau(x) n'` with `n'` in `N^G`. Writing
     `n' = tau(n)` gives `y = tau(xn)`.
4. **Base case.** An `F_p`-linear automaton on `(F_p^n)^G` that is injective is surjective when
   `M_n(F_p[G])` is directly finite. This is the standard equivalence between linear surjunctivity and
   stable finiteness (Ceccherini-Silberstein–Coornaert). The converse is
   `stable-finiteness-failure-refutes-surjunctivity`.

**Scope.**
- Nonabelian simple layers need a separate argument. A homomorphism `T^S -> T` with `T` nonabelian simple
  is trivial or a coordinate projection composed with an automorphism, since `T^2` does not embed in `T`.
  That forces permutation-type rules on such layers. Extending the reduction to all finite `K` is left
  open.
- **Consequence:** noncommutative group alphabets give no escape from the linear gates.

### 1.4 Stabilized Goodearl–Handelman certificates are Theorem E

The freedom to pass to `S_-^(n+1) -> S_-^n` summands, with `n` arbitrary, is already
`ternary-anti-central-unit-class-is-nonpositive`. It is equivalent to the corner equation by
`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`. Nothing new.

### 1.5 Halving the anti-central idempotent by group conjugates is impossible

- **An exact relation in G_3.** Put `k = s0 t0 - s1 t1` and `g = s1 t0 + s0 t1`. Then `k^2 = 1` and
  `g k g^-1 = zk`, with `z = -1` central. So `p = eps_-(1+k)/2` is an idempotent of `S_-`, and exactly
  `g p g^-1 = eps_- - p`.
- **The halving certificate.** Any state then has `s(p) = 1/2`. A halving `p = p_1 + p_2` with orthogonal
  `p_i ~ p` would force `s(p) = 2 s(p)`, so no state could exist.
- **Group conjugates cannot do it.** Suppose the `p_i = eps_-(1+k_i)/2` are conjugates of `p` by group
  elements. The sum condition becomes `eps_-(1 + k_1 + k_2 - k) = 0`: the element must be `z`-invariant.
  - The identity has coefficient 1 on the left.
  - On the right it would need `z k_i = 1` or `zk = 1`.
  - But `k` and its conjugates are not central, while `z` is.
- **So a halving must use non-monomial equivalences.** That is the corner equation again. Induced
  rank from finite subgroups blocks every monomial certificate built from finite-subgroup idempotents in
  the same way.

## 2. Plan 1 (rank 1): the state upgrade turns rank triviality into a counterexample

### 2.1 Statement

**Claim** `ternary-anti-central-states-force-nontrivial-rank-models` (OPEN). Let `G = G_3 = L_(F_3)(1,2)^x`
and `S_- = eps_- F_3[G]`. If `(K_0(S_-), [eps_-])` has a state, then `G` has a nontrivial
characteristic-three rank model.

### 2.2 Why it is decisive

Combine it with three landed nodes:
- `anti-central-state-obstruction-equals-stable-finiteness`: no state implies `k[eps_-] <= 0`, which
  refutes Gottschalk on `G_3`.
- `ternary-leavitt-rank-models-move-z-iff-nontrivial`: a nontrivial model is the same as one moving `z`.
- `leavitt-el3-rank-models-over-finite-fields-are-trivial` (OPEN), or any other proof of the "No" branch
  of `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`.

Then Gottschalk is refuted.

Today the "No" branch of the rank gate only gives non-linear-soficity of `G_3` and `PG`. With the upgrade
it becomes a counterexample. So every lane proving rank triviality (family R4, `w4-gate-descent`,
`w4-heisenberg`, `w3-gate-char3`) is also working toward a counterexample. The linear route then needs
no lifting construction at all: the corner equation follows from the absence of states.

### 2.3 The gap it closes

We have: rank models moving `z` give Sylvester matrix rank functions on `S_-`, which give states. The
plan asks for a partial converse, in two steps.

- **(U1) From a state to a rank function.** A state gives a Sylvester matrix rank function `N` on `S_-`
  with `N(eps_-) = 1`.
  - For von Neumann regular rings this is Goodearl's correspondence between pseudo-rank functions and
    `K_0` states.
  - **First lemma to try:** find a regular ring `U` and a map `S_- -> U` that is unital, `K_0`-order
    embedding with cofinal image, for instance a universal localization inverting the full matrices of
    `S_-`. Then states extend by Hahn–Banach and pull back as rank functions.
- **(U2) From a rank function to a rank model.** The rank completion of `(S_-, N)` is a regular rank
  ring, and `G` maps into its units, moving `z`. The plan needs a model inside a rank ultraproduct of
  matrix algebras.
  - The halving and root-element arguments of the gate artifacts use only additivity, invariance and
    subadditivity. So the first check is whether they already hold for abstract Sylvester rank functions.
  - If so, (U2) is unnecessary: replace "rank model" by "rank function" in the gate, and (U1) alone
    suffices.

### 2.4 What could kill it

- **A calibration ring.** A ring with the rank condition but no Sylvester matrix rank function would kill
  (U1) in general, though not for `S_-`. Search the literature first: Malcolmson, Schofield's
  *Representations of rings over skew fields*, and Jaikin-Zapirain's survey of rank functions.
- **A state not coming from any rank function.** A state on `S_-` that factors through a ring map to a
  ring with no rank function would kill (U1) for `S_-` itself.
- **Why sofic data cannot falsify it.** When `PG` is sofic, both sides hold, so sofic calibrations say
  nothing.

### 2.5 Payoff and ranking

- **Payoff.** It is a counterexample conditional only on the rank gate, which several families are
  already attacking.
- **Why rank 1.** It is the only plan found that makes an existing obstruction-side proof effort
  produce the counterexample directly.
- **Cost.** (U1) is ring theory with no group input. That is cheap to test, and a literature
  counterexample would end it fast.

## 3. Plan 2 (rank 2): diagonal covariance on the two-root defect piece

### 3.1 Statement

**Claim** `leavitt-two-root-defect-piece-forces-covariant-diagonal` (OPEN). Let `R = L_(F_2)(1,2)` and take
a characteristic-two rank model of `R^x` violating the two-root identity. On the defect piece
`Q = im(N'_23 N'_12)` of `leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model`, or on some
nested piece `Q_k`, the model carries a family of idempotents `e_w`, indexed by cylinders `w`, such that:
- `e_(w0) + e_(w1) = e_w`, with the two summands orthogonal;
- for `v` in `V` intersected with the nine-leaf subgroup, acting by prefix replacement on `w`,
  `sigma(v) e_w sigma(v)^-1 = e_(v.w)`;
- `rk(e_w) > 0` for some proper `w`.

### 3.2 Why it is decisive

- **The obstruction.** By `thompson-v-cantor-system-has-no-covariant-rank-model`, no covariant family of
  this kind exists: all proper cylinders then share one rank `c`, and `c = 2c`.
- **So the defect vanishes.** The claim contradicts `delta > 0`, which gives `N_23 N_12 = 0` in every
  char-2 rank model. By corner locality that is `leavitt-el3-rank-models-over-finite-fields-are-trivial`
  in characteristic two.
- **Binary payoff.** `R^x` is not `F_2`-linear sofic, the first non-linear-sofic group.
- **With Plan 1's ternary analogue** it would also feed the ternary counterexample route.

### 3.3 First lemma to try

For a pair of disjoint cylinders `(w, w')` with nonempty complement, put `V_(w,w')` = the span of the
images of `sigma(1 + s_w y t_(w')) - 1` over `y` in `R`.
- **Covariance.** `sigma(v) V_(w,w') sigma(v)^-1 = V_(vw, vw')` exactly, since
  `v s_w y t_(w') v^-1 = s_(vw) y t_(vw')` when `v` replaces prefixes.
- **Refinement.**
  - `V_(w0,w') <= V_(w,w')`, because the root group at `(w0,w')` sits inside the one at `(w,w')`.
  - `V_(w,w') <= V_(w0,w') + V_(w1,w')`, because `s_w y t_(w') = s_(w0)(t_0 y)t_(w') + s_(w1)(t_1 y)t_(w')`.
    The two terms have product zero, so `N_(A+B) = N_A + N_B + N_A N_B`.
- **If these spans have well-defined ranks** (a finiteness issue: joins of countably many idempotents need
  not exist in a rank ultraproduct), transitivity gives them one common rank `c`. The inclusions then
  force `rk(V_(w0,w') cap V_(w1,w')) = c`, so the refined images coincide up to rank zero.

What remains:
- **Corner locality.** Triviality holds iff `rk(n_23(s_0) n_12(t_0)) = 0`. Combine it with coinciding
  images, and the dual statement for kernels, to show that the defect product has rank zero.
- **Idempotents.** Alternatively, produce the orthogonal idempotents `e_w` from the image spaces on `Q`.
  Coinciding images alone are not orthogonal, so orthogonality is the missing input.

### 3.4 What could kill it

- **The join issue.** It can kill the span ranks. Replace spans by finitely generated sub-root-groups,
  and check that covariance survives.
- **The Toeplitz Kazhdan group.** `kazhdan-groups-without-fd-reps-violate-two-root-identity` violates the
  identity. Any mechanism proving the identity must fail there. Its coefficient algebra `C(X,F_2) ⋊ Z`
  has no Leavitt halving, so check that the argument really uses `s_0, s_1`.
- **The adversary.** Ask `w4-r4-adversary` to attack the mechanism.

## 4. Review corrections and the sharpest form of Plan 1

### 4.1 Plan 1: which parts of (U2) can be skipped

**w3-gate-char3** (1bace02f7e, its artifact Section 7). The characteristic-three gate results hold for any
`F_3`-algebra whose Sylvester matrix rank function is positive on nonzero idempotents:
- the equivalences between z-moving, nontrivial, injective and anti-central models;
- the corner kill;
- the Haar law;
- the torus normal form.

The one exception is the transfer to `PG`, which uses Kronecker products and Jordan forms and is not used
here. **Corollary 7.2:** a rank function `N` on `S_-` with `N(eps_-) = 1` is itself an anti-central model,
in `S_-/ker N`. So (U2) can be skipped, at the price of proving the "No" branch for abstract rank algebras.

**w3-strategist-gate (R4 lead).**
- **Soft parts transfer to abstract rank functions:** the endpoint
  `toeplitz-isometry-defects-have-total-rank-at-least-one`, the el4 normal-closure lemma, the
  reversed-root identity and both firewalls.
- **Hard parts do not:** the defect gap, descent and opposite-root positivity are stated only for faithful
  rank ultraproducts in characteristic two, with no characteristic-three counterpart.

So nothing in R4 is yet evidence for the abstract ternary "No" branch.
### 4.2 Plan 2: the first lemma of Section 3.3 cannot produce the `e_w`

**(a) Spans are refinement-invariant.** In a regular rank ring with faithful rank, if one submodule sits
inside another with equal rank, they are equal: a complement would have rank zero, hence be zero.
- **First coordinate.** Section 3.3 gives `V_(w0,w') <= V_(w,w')` with equal ranks, so
  `V_(w0,w') = V_(w,w') = V_(w1,w')`.
- **Second coordinate.** The same holds there, from
  `s_w y t_(w') = s_w (y s_0) t_(w'0) + s_w (y s_1) t_(w'1)`.

So the image spans do not change under refinement and cannot be the orthogonal halves `e_w`. As the R4
lead put it, orthogonality is block support under another name.

**(b) The locally finite subgroup cannot supply orthogonality.** This kill test is due to the R4 lead.
- **The subgroup.** Root elements at `(w0,w')` and at `(w1,w')` commute. Both cross terms contain
  `t_(w') s_(w0)` or `t_(w') s_(w1)`, which vanish because `w'` is disjoint from `w`. In characteristic
  two each root element is an involution, so the two root groups generate an elementary abelian 2-group
  `H_0 x H_1`.
- **The kill.** In the regular model of `H_0 x H_1`, the two augmentation images meet in rank
  `(1 - 1/|H_0|)(1 - 1/|H_1|) > 0`. So relations inside that subgroup never force orthogonality.
- **Consequence.** Any orthogonality proof has to use `sigma` outside it, most likely the prefix
  replacements that do not preserve measure.


**(c) The adversarial audit makes Plan 2 a reformulation.** This is `w4-r4-adversary`, a597ebfc50,
`research/artifacts/covariant-diagonal-plan-adversarial-audit-2026-09-12.md`.
- **Joins exist.** Kill test (a) fails: countable saturation gives joins and meets of principal right
  ideals in rank ultraproducts.
- **Monotone rigidity.** `covariant-monotone-cylinder-families-in-rank-models-are-constant`: every
  V-covariant, refinement-monotone family of principal ideals indexed by proper cylinders is constant.
- **The claim is the gate.** Covariant orthogonal cylinder idempotents are zero in every model and every
  nonzero corner. So the conclusion of `leavitt-two-root-defect-piece-forces-covariant-diagonal` holds in
  no model, and the claim is equivalent to the characteristic-two gate. The first lemma is an automatic
  instance of rigidity, true whatever the defect.
- **Root spans give only the known direction.** The all-coefficient identity on one frame forces
  triviality, through a Weyl element and simplicity.
- **The Toeplitz test is consistent.** Its invariant trace forbids depth-changing units, so honest diagonals
  exist there.
- **What a proof needs.** A rank-halving inequality between consecutive depths for a non-span piece built
  from the defect.

**Plan 2's rank-2 ranking is withdrawn.** It is a reformulation of the gate, not a new reduction. Its useful
residue is the rigidity theorem, which belongs to the adversary lane, and the calibration of Section 4.3.

### 4.3 Calibration: in characteristic three, covariance is free but additivity becomes XOR

Let `G_3 = L_(F_3)(1,2)^x` and `r_w = 1 + s_w t_w` for a cylinder `w`.
- **Involutions.** In characteristic three, `(1+p)^2 = 1 + 3p = 1` for an idempotent `p`, so `r_w` is an
  involution of `G_3`. The empty word gives `r_() = 2 = z`.
- **Covariance.** A prefix replacement `v` whose domain partition is refined by `w` gives
  `v r_w v^-1 = r_(vw)`.
- **Multiplication.** `r_(w0) r_(w1) = r_w`.
- **The idempotents.** For any char-3 rank model `sigma`, put `e_w = sigma(r_w) - 1`. Then
  `e_w^2 = 2 - 2 sigma(r_w) = e_w`, since `-2 = 1`. So `e_w` is the `-1` eigenprojection, and it is exactly
  covariant.
- **The relation.** Expanding `sigma(r_w) = sigma(r_(w0)) sigma(r_(w1))` gives
  `e_w = e_(w0) + e_(w1) + e_(w0) e_(w1)`, the XOR of two commuting idempotents in characteristic three.
  So `rk(e_w) = rk(e_(w0)) + rk(e_(w1)) - 2 rk(e_(w0) e_(w1))`.
- **Ranks.** The involutions `r_w` for proper cylinders are all conjugate in `G_3`: `s_w t_w` and its
  complement are nonzero idempotents in the purely infinite simple ring `R`, which has `K_0 = 0`. So
  every proper `e_w` has one rank `c`.
  - **At the root:** `r_([0]) r_([1]) = z`. In a model with `sigma(z) = -1` this gives `1 = 2c - 2 rk(e_0 e_1)`.
  - **Below the root:** `c = 2c - 2 rk(e_(w0) e_(w1))`, so `rk(e_(w0) e_(w1)) = c/2`.
  - **Solution:** with `c = 1/2`, the rank w3-gate-v reports for the anti-central lifts, the top pair is
    complementary and every deeper pair overlaps in rank 1/4.

This is consistent with the Haar-measure picture of `w3-gate-char3` (6601af31f): nothing contradicts it.

**Moral.** Natural covariant cylinder families exist, but they satisfy the XOR relation, not orthogonal
additivity, and the halving obstruction needs additivity. So a proof of Plan 2 must turn an XOR family into
an additive one, or get orthogonality some other way, using elements outside the locally finite root
subgroups. Characteristic two has no `r_w` at all, since `1 + s_w t_w` is not a unit there.

### 4.4 The sharpest form of Plan 1: rank condition versus rank functions

Let `G = L_(F_3)(1,2)^x` and `S_- = eps_- F_3[G]`. Consider three conditions.
- **(C)** `S_-` fails the rank condition, `[eps_-] <= 0`. This is the counterexample,
  `ternary-anti-central-unit-class-is-nonpositive`.
- **(NS)** `(K_0(S_-), [eps_-])` has no state.
- **(NR)** `S_-` has no Sylvester matrix rank function with `N(eps_-) = 1`.

**Facts.**
- **(C) iff (NS).** This is `anti-central-state-obstruction-equals-stable-finiteness`, Goodearl–Handelman
  form.
- **(NS) implies (NR).** A normalized rank function restricts to a state on projections.
- **(NR) is a statement about the whole group algebra.** (NR) iff every Sylvester matrix rank function on
  `F_3[G]` has `rk(1 - [z]) = 0`. For one direction, `rk(eps_-) = t > 0` gives `N(X) = rk(eps_- X)/t`. For
  the other, `rk(X) = N(eps_- X)` extends `N`, because `eps_-` is central. This is
  `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`.
- **(NR) is the abstract "No" branch.** (NR) iff `G` has no anti-central model in an abstract rank
  algebra: Corollary 7.2 in one direction, pullback along `F_3[G] -> B` in the other. It implies the matrix
  "No" branch.
- **(U1) closes the gap.** (U1), `ternary-anti-central-states-give-sylvester-rank-functions`, is exactly
  (NR) implies (NS).

**Conclusion.** Given (U1), the linear ternary counterexample is equivalent to (NR): every Sylvester rank
function on `F_3[G]` kills `1 - [z]`. The route is
`ternary-counterexample-from-rank-kill-and-state-realization`.

**The risk.** A ring can satisfy the rank condition without having a Sylvester matrix rank function. That is
plausibly the general situation, though not checked against the literature here. If it happens for `S_-`,
then (NR) holds but gives no counterexample, and the corner equation must be attacked directly. So the
first task for (U1) is the literature, and the second is input specific to `S_-`.
