---
rg: 2
id: hs-expander-block-decomposition
kind: claim
title: Normalized-HS analogue of Kun's expander decomposition
distinct_from:
  commutant-no-growth: That is an exact statement about genuine finite-dimensional representations; this asks for a quantitative almost-invariant block partition of an almost-representation, where no genuine representation exists.
  invariant-size-collapse: That records that a conjugation-invariant strictly monotone size forces a compression to be an equality; this asks for the block structure that would manufacture such a size for normalized-HS almost-representations, which the bare trace does not provide.
  leavitt-steinberg-hs-stable: That is a branch selection for one explicit group; this is a general decomposition property of Kazhdan groups which would imply it.
  wreath-flexible-hs-stability: That is a stability statement for a specific wreath candidate; this is a structural decomposition for arbitrary Kazhdan groups and does not by itself assert any stability.
artifacts:
  - docs/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
  - docs/TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md
  - docs/NOTEPAD.md
---

Let `Gamma` have property `(T)` with Kazhdan pair `(S,kappa)`.  Ask for a
function `eps(delta) -> 0` as `delta -> 0`, depending only on `(S,kappa)`,
such that every `delta`-almost representation `phi:Gamma -> U(d)` in
normalized Hilbert--Schmidt norm admits a projection `p in M_d` with
`tau(1-p) <= eps(delta)` and an orthogonal decomposition
`p = p_1 + ... + p_k` for which

- each block is almost invariant:
  `sum_i ‖[phi(s),p_i]‖_2^2 <= eps(delta)` for every `s in S`; and
- each block carries a uniform spectral gap, in the following exact form:
  writing `tau_i = tau(.)/tau(p_i)` for the normalized trace on
  `p_i M_d p_i` and `u_s = p_i phi(s) p_i`,

```text
sum_(s in S) ‖u_s x - x u_s‖_(2,p_i)^2 >= kappa'^2 ‖x - tau_i(x) p_i‖_(2,p_i)^2
```

  for every `x = x^*` in `p_i M_d p_i`, with `kappa'>0` depending only on
  `(S,kappa)`; and

- the blocks drift correctly under each compressor: for every `t` with
  `t Gamma t^(-1) <= Gamma` and every fine block `p_j` there is a single
  fine block `p_(sigma(j))` with

```text
‖phi(t) p_j phi(t)^* - p_(sigma(j))‖_2 <= eps(delta),
    tau(p_(sigma(j))) >= tau(p_j) - eps(delta).
```

The last clause was originally left to the consuming routes as a prose
caveat.  It is folded into the statement here because a route may not assert
an implication it does not establish, and both consumers need exactly this
and nothing weaker.

**The former compressed-unitary bookkeeping debt is gone.**  An earlier
version attached an extra obligation to pass from the compressed operators
`p_i phi(s) p_i` to genuine unitaries before applying a Cheeger inequality.
The current consumer `tracial-median-from-block-decomposition` bypasses that
step: `median-poincare-concentration` is applied directly to the displayed
Poincare inequality for the compressed operators.  No separate unitary
rounding or spectral-coarea error term is required by that route.  What
remains here is therefore the decomposition, the block gap, nesting, and
compressor transport themselves.

Neither `k` nor the traces `tau(p_i)` are constrained; blocks of vanishing
normalized trace are allowed, as they are in the permutation case.

**A nested pair is needed, not one decomposition.**  Reading the argument
this transcribes (`official/counterexample.tex:310-371`) shows it applies
Kun's theorem **twice**, to `Gamma` and to the ambient `G=<Gamma,t_1,...,t_m>`,
and uses both at once: the fine `Gamma`-blocks define the size observable,
while the coarse ambient `G`-blocks supply the normalizing medians, one per
ambient block.  The Lean instantiation does the same
(`KunFixedDecomposition.expanderDecomposition` applied to `A.comap embedGamma`
and to `A`).  So what is being asked for here is a **nested** pair of block
algebras `B_G <= B_Gamma`, the coarse one almost invariant under all of `G`
and the fine one under `Gamma`, both with uniform gap.  Nesting matters
operator-theoretically and not just bookkeeping: the size observable and the
ambient projections must commute for the fiberwise functional calculus
below to be defined, which is automatic for functions on a set and is a
genuine demand on a tracial model.

This is the exact normalized-HS transcription of Kun, *On sofic
approximations of property (T) groups*, arXiv:1606.04471, which supplies it
for sofic approximations: there the blocks are the connected components of
the `S`-labelled Schreier graph, the almost-invariance is exact off `o(|Y|)`
vertices, and the gap is uniform Cheeger expansion.  In that setting the
block algebra exists for free, because a permutation model acts on a *set*
and `l^infinity(Y)^Gamma` is atomic by construction.  A unitary model has no
distinguished maximal abelian subalgebra, and an almost-representation has
no isotypic decomposition, so the block algebra has to be produced rather
than read off.

The statement is close to, but not the same as, Alekseev--Thom's Open
Problem 6.2 (arXiv:2608.05362), which asks for finite-dimensional
`*`-subalgebras whose tracial ultraproduct is exactly the commutant of a
Kazhdan group's ultraproduct image, and in part (b) asks whether they can be
realized as exact centralizers of chosen generator lifts.  **A positive
answer to 6.2(b) does not by itself supply this claim.**
`rank-one-lift-perturbation-gap-no-go` gives a Kazhdan example where the
finite-level exact centralizers capture the ultraproduct commutant in the
strongest possible scalar form while the adjoint Poincare constant of their
only minimal block tends to zero.  The missing strengthening is therefore
Hilbert-space `L2` control/uniform integrability of almost-central vectors,
or an explicit finite-level gap statement, not merely algebraic centralizer
capture.  Conversely, this claim does not ask to capture the whole
ultraproduct commutant.

Two cautions recorded so the statement is not weakened into triviality.

- **The ultraproduct form is false.**  Take `Gamma=SL_3(Z)`, `phi_n` the
  left regular representation of `SL_3(Z/nZ)` pulled back along reduction.
  These are genuine representations, so `delta=0`.  Their commutants are the
  right regular algebras `C[SL_3(Z/nZ)]`, whose minimal projections have
  normalized trace `d_pi/|G_n| <= |G_n|^(-1/2) -> 0`; hence the tracial
  ultraproduct of the commutants is diffuse and admits no atoms at all.  So
  the decomposition can only be asked for at each finite level, with
  constants uniform in `d`, and any proof that passes to the ultraproduct
  first has already lost the block structure.
- **Genuine representations satisfy the gap clause after splitting into
  irreducible summands**, not merely isotypic components.  On an irreducible
  summand the adjoint representation has only the scalar fixed vectors, so
  property `(T)` supplies the uniform gap.  An isotypic component with
  multiplicity greater than one still has a matrix-valued commutant and does
  not satisfy the scalar Poincare inequality as stated.  Thus all the real
  content remains at `delta>0`, where no irreducible decomposition is
  available.
- **At finite level atomicity is automatic**, since every subalgebra of
  `M_d` is atomic.  The issue is not a uniform lower bound on atom traces --
  the statement explicitly permits vanishing-trace blocks.  The issue is a
  dimension-uniform Poincare gap on the chosen atoms together with
  vanishing total boundary and coherent transport/nesting even when their
  traces go to zero.  Diffuse ultraproduct commutants are the symptom of why
  bare finite-level atomicity does not provide that uniform structure.

## The exact case collapses, so the difficulty is entirely the error term

If the invariant algebra were exact, everything above is free.  Let `A` be a
finite-dimensional abelian unital subalgebra of `M_d` commuting with a
genuine `phi(Gamma)`, with atoms `p_1,...,p_k`, and let `u=phi(t)` for a
compressor.  From `t Gamma t^(-1) <= Gamma`, equivalently
`Gamma <= t^(-1) Gamma t`, any `a` commuting with `phi(Gamma)` has `u^*au`
commuting with `phi(t^(-1) Gamma t) >= phi(Gamma)`, so `u^*Au <= A`.  The map
`theta(a)=u^*au` is then a unital `*`-endomorphism of `A ~= C^k`, injective
because conjugation is injective on `M_d`.  Unital `*`-endomorphisms of
`C^k` are dual to self-maps `sigma` of the `k` atoms, and injectivity of
`theta` is surjectivity of `sigma`; a surjective self-map of a finite set is
a bijection.  Hence `u^*Au = A`, the atoms are permuted,
`theta(p_j)=p_(sigma^(-1)(j))`, and

```text
tau(p_(sigma^(-1)(j))) = tau(u^* p_j u) = tau(p_j),
```

so the block traces are preserved exactly and no median device is needed.

This is `invariant-size-collapse` wearing a different hat -- the atom count
is the conjugation-invariant strictly monotone size, and it exists here only
because the algebra is atomic with finitely many atoms.  The consequence for
this claim is worth stating plainly: **the whole difficulty is the
approximation error, not any genuine inequality of block traces.**  In the
exact world traces come out equal for free; the median device of
`tracial-median-concentration` exists solely to recover that conclusion from
an almost-invariant algebra.

## Why the Pimsner--Popa index is not the invariant here

Offered by cairn-wall, whose lane uses it to real effect
(`compressor-growth-index-homomorphism`,
`commutator-compressor-carries-no-wall`), on the ground that the index
tolerates unequal traces where a minimal-projection count does not.  It does
not transfer to this claim, and the reason is worth recording so it is not
re-attempted.

For finite-dimensional abelian `N <= M` with atoms `e_i` of `N` and `f_j` of
`M`, the trace-preserving conditional expectation gives
`lambda = min_j tau(f_j)/tau(e_(i(j)))`, so

```text
Index(M,N) = max_j tau(e_(i(j)))/tau(f_j).
```

That is indeed a genuine "how unequal are the pieces" quantity, and on
**exact** inclusions it is exactly what cairn-wall needs -- it is
multiplicative along the compression semigroup and can be cancelled across a
group relation.  But it is **discontinuous in the metric this claim lives
in**.  Refining a single atom of trace `t` into pieces of trace `t-eps` and
`eps` moves the subalgebra by `O(sqrt(eps))` in `‖.‖_2` -- the new atom has
`‖e''‖_2 = sqrt(eps)` -- while sending the index to at least `t/eps`.  So the
index blows up on refinements that are metrically invisible, which is the
same failure mode as the atom count and is precisely the regime the median
device exists to control.  An almost-invariant block algebra has no exact
inclusion to take the index of in the first place.

The quantity that does survive is the median-normalized size observable of
`tracial-median-concentration`: `f = M(M+m_A)^(-1)` is a continuous
functional calculus of a positive contraction, hence `‖.‖_2`-stable, and its
concentration is exactly the unequal-trace statement.

## An operator-norm strengthening would be a dichotomy, not a variant

`bounded-rank-corners-excluded` (cairn-torsionfree) does not constrain this
claim as stated -- these blocks are almost invariant in normalized
Hilbert--Schmidt norm, which does not place them in the exact operator-norm
relative commutant, and vanishing normalized trace is explicitly allowed.
But it interacts sharply with the **gap** clause if anyone strengthens the
almost-invariance to operator norm, and the interaction is worth recording
before someone tries.

Over a minimally almost periodic Kazhdan source such as `St_5(L)`, a
bounded-rank projection in the exact relative commutant has finite-dimensional
invariant range, hence gives a genuine finite-dimensional unitary
representation, hence a **trivial** action on that range.  Now impose the gap
clause on such a block: with `u_s = p_i` for every `s`, the left-hand side of
the displayed inequality is `0`, so `x = tau_i(x) p_i` for every
`x` in `p_i M_d p_i`, i.e. `rank(p_i)=1`.  So in an operator-norm version

- every bounded-rank block is forced to have rank exactly one, and
- if the whole fine decomposition consists of bounded-rank blocks, it is a
  **masa**.

The second horn is not a comfortable place to arrive.  A `phi(Gamma)` almost
normalizing a full masa is the hypothesis of Theorem 9 of
`docs/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md`, which concludes that a
masa-normalizing tracial model contains a permutation model of comparable
defect -- for a nonsofic group, a contradiction.  So an operator-norm
strengthening must produce blocks of unbounded rank, and cannot terminate in
small blocks.  Stated as a caution rather than a theorem: Theorem 9 carries
its own hypotheses (`(F,eps)`-multiplicativity, `def_D(phi(g)) <= delta`,
and correctly carried lamp data) and is written for the Kun--Thom pair, so
the second horn needs checking against those before it is used.

## Placement of the Kazhdan projection-rounding theorem

`kazhdan-projection-rounding` (cairn-wall) proves that for a genuine
`pi:G -> U(M)` with `M` finite tracial and `N = M cap pi(Gamma)'`, every
projection `p` in `M` has a projection `q` in `N` with
`‖p-q‖_2 <= (1+sqrt 2) kappa^(-1) max_s ‖[pi(s),p]‖_2`.  Verified here
independently: `a=E_N(p)` satisfies `tau(pa)=tau(a^2)` and `tau(a)=tau(p)` by
bimodularity and trace preservation, giving the exact identity
`‖p-a‖_2^2 = tau(a(1-a))`; and `(t-chi_([1/2,1])(t))^2 <= 2t(1-t)` holds on
`[0,1]` -- at `t<1/2` it reduces to `t <= 2/3` and at `t>=1/2` to `t >= 1/3`
-- so cutting `a` at `1/2` costs a further `sqrt 2` factor.  The constant is
right.

Where it lands for this claim is the point.  Its proof needs `pi` to be a
genuine homomorphism, both for `L^2(N)` to be the fixed space and for `(T)`
to apply, so it lives on the **ultraproduct** side -- which is exactly the
side where the displayed `SL_3(Z)` example shows the block structure has
already been destroyed.  It is therefore not a tool for building the
decomposition at finite level, which is where this claim has to be proved.

One thing it is **not** needed for.  Its stated residual obstruction -- that
one would still have to rule out projections of intermediate trace in `N` --
does not apply to the consumer here.  The Cheeger step of
`tracial-median-from-block-decomposition` never forces `tau(P)` toward `0`
or `1`; it lower-bounds boundary energy by `min(tau_q(P), tau_q(q-P))`, which
is what the threshold integral consumes.  That obstruction answered an
earlier and cruder form of the question, superseded once the block gap was
shown to *be* the Cheeger inequality.

## Why offered tools keep landing on the wrong side

Three have been offered from neighbouring lanes and all three miss for the
same structural reason, which is worth stating once so it is not rediscovered
a fourth time.  The Pimsner--Popa index needs an **exact inclusion**.
`kazhdan-projection-rounding` needs a **genuine homomorphism**.
`coordinate-ultraproduct-transport` needs **operator-norm** asymptotic
multiplicativity, since a small `‖.‖_2` defect gives no control on individual
vectors and so assembles no honest representation on the coordinate
ultraproduct.

This claim lives at finite level, in normalized Hilbert--Schmidt norm, with
only approximate invariance -- the one corner of the square where none of
those three hypotheses is available.  That is not bad luck about which tools
happen to exist.  It is a restatement of why the fork is open: every
rigidity tool in the corpus buys its conclusion with exactness, in the
metric, in the algebra, or in the homomorphism, and the Leavitt--Steinberg
question is precisely the one that denies all three at once.

**A genericity claim made here earlier was wrong and is retracted.**  It read:
because the index diverges whenever minimal projections have vanishing
trace, any model with diffuse limiting commutant has infinite index, so the
infinite-index regime is generic.  Two errors.  A diffuse algebra has **no**
minimal projections at all, so the finite-dimensional formula above does not
apply to it; and diffuseness alone does not force infinite index, since a
finite-index subfactor of a `II_1` factor is diffuse.  What the computation
actually supports is the *discontinuity* statement -- a scope limit on using
the index as a metric invariant -- and nothing about diffuse limits.

The nearest true statement is narrower: if `N` is diffuse **abelian** in a
`II_1` factor `M` then `[M:N]=infinity`, because `N <= N' cap M` makes the
relative commutant infinite-dimensional while a finite-index inclusion has
finite-dimensional relative commutant.  The commutant in the `SL_3(Z)`
example is `prod_omega C[SL_3(Z/n)]`, which is diffuse but **not** abelian,
so even that statement does not cover it.

**Nor is the index the right target functional on an exact nesting.**  For a
finite-dimensional abelian nesting with `B_1`-atoms `p_i` and `B_0`-atoms
`q_A = sum_(i in A) p_i`, the correct formula is

```text
[B_1:B_0] = max_A ( sum_(i in A) tau(p_i) ) / ( min_(i in A) tau(p_i) )
          >= max_A #A,
```

with equality inside a block exactly when its fine atoms have equal trace
(cairn-wall, Proposition 4a; the derivation is `E(p_i) =
(tau(p_i)/tau(q_(A(i)))) q_(A(i))` and then `x=p_i` in the Pimsner--Popa
definition).  The formula is right, but the proposed reformulation of
`tracial-median-concentration` as `[B_1:B_0] / max_A #A -> 1` is **not**
equivalent to it, and the failure is in the useful direction.  Take one
coarse block with `k` fine atoms all of trace `t`, and a second with two
fine atoms of traces `10s` and `s`.  Then the first block contributes `k`,
the second contributes `11`, so for `k >= 11` the index is exactly `k` and
`max_A #A = k`: the normalized quantity is exactly `1` while the second
block has trace ratio `10`.  Taking maxima over coarse blocks discards
precisely the per-block information the median device is about.

A second mismatch points the same way.  The manuscript's `(8)` is a
statement *after discarding an exceptional set of vanishing trace*, whereas
the index is a bare maximum: one tiny unbalanced block leaves `(8)`
untouched and sends the index up.  So the two are incomparable in both
directions, and minimizing the index is not a proxy for the target.

## Current finite-level frontier: the spike regime

The nearby Cairn claims now isolate one local obstruction more sharply than
the older prose above.

- `bounded-low-gap-witness-gives-balanced-cut` proves that a self-adjoint
  low-adjoint-energy witness with a fixed operator-norm bound produces a
  quantitatively balanced almost-invariant spectral projection.
- `low-gap-witness-spike-or-balanced-cut` removes that boundedness
  assumption: after clipping at any fixed height `C`, either one gets such a
  balanced cut, or a fixed fraction of the witness's `L2` mass is carried by
  a projection of trace `O(C^-2)`.
- `rank-one-lift-perturbation-gap-no-go` shows the second alternative is not
  cosmetic.  Vanishing-rank directions can destroy every finite-level gap
  while disappearing in the tracial algebra ultraproduct.

So a finite-level proof cannot end with ordinary tracial-ultraproduct
centralizer capture.  It must control the **uniform integrability of
normalized almost-central vectors** (or replace it by an equally strong
finite-level statement) and then organize the resulting cuts without losing
nesting or compressor transport.  This is the live analytic subproblem left
by the current Cairn neighborhood; bounded witnesses and bare algebraic
centralizer capture are already accounted for.

## Prior statement in the corpus

This node imports and sharpens a diagnosis the corpus already reached for a
different target.  `docs/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md:407-412` names
it verbatim as the decisive open sub-claim:

> any Hilbert--Schmidt analogue of Kun--Thom Theorem 4.1 (normalization of
> the centralizer of a Kazhdan sofic approximation).  Their proof runs on
> connected-component vertex masses and isotropy orders of a finite cluster
> groupoid; a hyperlinear approximation of a Kazhdan group has a spectral gap
> for the adjoint action, but its fixed algebra need not be atomic and
> carries no component sizes.  This is the decisive open sub-claim.

`docs/NOTEPAD.md:21875-21881` reaches the same conclusion in weaker form.
What is added here is the statement as a decomposition claim with its
quantifiers, the finite-level caveat above, and the wiring into the
Leavitt--Steinberg fork.  The transfer is by analogy of method, not by
implication: the cited file is written for the Kun--Thom wreath / Clifford
lamp target, not for `St_5(L)`.

Two further corpus facts bear directly on the shape of a proof.

- **Do not obtain the blocks by normalizing a masa.**
  `docs/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md` Theorem 9 (`:323-336`) shows
  that a masa-normalizing tracial model contains a permutation model of
  comparable defect, so that relaxation is *equivalent to* soficity rather
  than weaker, and buys nothing.  Its Proposition 11 (`:348-368`) is the
  usable half: if a subalgebra with `k` atoms **of equal trace** is
  normalized to within `delta`, then `u` is `3 sqrt(delta)`-close to
  `U(N/k) wr Sym(k)` and the induced map on `k` points is Hamming-almost
  multiplicative.  So the equal-trace case of this claim already converts to
  a permutation model, which is why the unequal-trace case, handled in the
  permutation argument by the median device, is the substance.
- **One neighbouring step already has a proved HS analogue.**
  `docs/TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md` `(SCI2)` proves
  `integral_0^1 ‖[P_t,A]‖_2^2 dt <= ‖[H,A]‖_2 ‖A‖_2` for spectral
  projections `P_t` of a positive contraction, the normalized-HS analogue of
  the graph coarea identity `Matching/FiniteGraph.coarea`, with a
  common-threshold form `(SCI5)` for finitely many arrows.  This is evidence
  that the permutation layer is not uniformly untranslatable, and is the
  natural tool for producing a single almost-invariant cut once a candidate
  positive contraction is in hand.
