---
rg: 2
id: every-group-has-positive-rokhlin-entropy-action
kind: claim
title: Every countably infinite group has a free ergodic p.m.p. action of positive Rokhlin entropy
root: true
distinct_from:
  gottschalk-surjunctivity-conjecture: that is surjunctivity of cellular automata; this is an entropy existence statement from which Seward's Krieger II derives surjunctivity, with no converse known.
  bernoulli-shift-entropy-classifies-for-every-group: that is the classification of Bernoulli shifts by base entropy; this is the positive-entropy hypothesis from which Seward derives the equality of Bernoulli Rokhlin entropy with base entropy.
refuted_by:
  - leavitt-unit-group-nonsurjunctive
---

**OPEN.** Every countably infinite group `G` admits a free ergodic
probability-measure-preserving action with positive Rokhlin entropy.

**Source.** B. Seward, *Krieger's finite generator theorem for actions of
countable groups II*, arXiv:1501.03367. The abstract, read on 2026-09-12:
"Under the assumption that every countable group admits a free ergodic action
of positive Rokhlin entropy, we prove that: (i) the Rokhlin entropy of a
Bernoulli shift is equal to the Shannon entropy of its base; (ii) Bernoulli
shifts have completely positive Rokhlin entropy; and (iii) Gottschalk's
surjunctivity conjecture and Kaplansky's direct finiteness conjecture are
true."

**Why it is a root.** One statement implies:
- `gottschalk-surjunctivity-conjecture`;
- Kaplansky direct finiteness, whose counterexample side is
  `leavitt-unit-group-algebra-not-directly-finite`;
- `bernoulli-shift-entropy-classifies-for-every-group`.

It can only fail on nonsofic groups. Seward, arXiv:1805.08279, introduction:
"The Rokhlin entropy of the Bernoulli shift G↷(L^G,λ^G) is H(L,λ) when G is
sofic but when G is not sofic its value is not yet known."

## Wiring

Read from the PDF of arXiv:1501.03367 on 2026-09-12. For a countably infinite
group `G`, Seward names three statements:
- **POS:** some free ergodic p.m.p. action of `G` has positive Rokhlin entropy;
- **INF:** `h^Rok_sup(G) = ∞`;
- **RBS:** `h^Rok_G(L^G, λ^G) = H(L, λ)` for every standard probability space
  `(L, λ)`.

The per-group implications INF ⟹ RBS ⟹ Gottschalk and Kaplansky direct
finiteness for `G` are recorded in
`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`. Seward, §1: "We do not
know whether POS implies INF." Theorem 1.11 makes the universal forms coincide:
"Let P be a countable group containing arbitrarily large finite subgroups. If G
is any countably infinite group with h^Rok_sup(G) < ∞ then h^Rok_sup(P × G) = 0.
Thus (∀G POS)⇒(∀G INF)." So this root is equivalent to ∀G INF, and hence to
∀G RBS.

Routes out of this claim:
- `every-group-positive-rokhlin-gives-leavitt-unit-case`, into
  `leavitt-unit-group-has-positive-rokhlin-entropy-action`;
- `every-group-positive-rokhlin-gives-tester-host-case`, into
  `tester-host-has-positive-rokhlin-entropy-action`. Composed with
  `positive-rokhlin-entropy-on-one-host-proves-gottschalk`, this gives
  Gottschalk's conjecture for every group.

On those hosts POS and INF coincide, by
`rokhlin-supremum-dichotomy-with-centralized-self-copies`.

## Refutation

`refuted_by: leavitt-unit-group-nonsurjunctive`. If `U = L_(F_2)(1,2)^×` is not
surjunctive:
- RBS(U) fails, by the contrapositive of Seward, Corollary 4.1 ("Assume that
  h^Rok_G(k^G, u^G_k) = log(k) for every k ∈ N. Then G satisfies Gottschalk's
  surjunctivity conjecture");
- so INF(U) fails, since INF ⟹ RBS for each group;
- so ∀G INF fails, and this root fails by Theorem 1.11.

The same chain refutes this root from any group that is not surjunctive,
including any group whose group algebra over a finite field is not stably
finite (`stable-finiteness-failure-refutes-surjunctivity`). Cairn fires
`refuted_by` only once the refuter is established.

Proving this root is therefore at least as hard as Gottschalk's conjecture for
all groups. A counterexample to Gottschalk or to Kaplansky direct finiteness
anywhere refutes it.

## Attempts

- **Origin.** The strategy lane `opportunity-mapper` opened this claim (item 1
  of `research/artifacts/opportunity-map-2026-09-12.md`). The lane
  `rokhlin-entropy` read the per-group statements and did the wiring above.
- **Host-level failure modes are recorded elsewhere.** Sofic entropy,
  restriction to sofic subgroups, co-induction and small free factors are on
  `leavitt-unit-group-has-positive-rokhlin-entropy-action`. A lower bound for
  one nonsofic host is at least as hard as that host's surjunctivity
  (`positive-rokhlin-entropy-makes-leavitt-units-surjunctive`).
- **Factor maps give no lower bound.** Bowen, arXiv:0812.2718, abstract: "if G
  is a countable group that contains a nonabelian free subgroup then every pair
  of nontrivial Bernoulli shifts over G are weakly isomorphic." Rokhlin entropy
  is not monotone under factors. Over the sofic group `F_2`, the 2-shift and the
  4-shift have Rokhlin entropy log 2 and log 4 (sofic entropy bounds Rokhlin
  entropy below and base entropy bounds it above), yet the 2-shift factors onto
  the 4-shift (Ornstein–Weiss). Weak isomorphism therefore transfers nothing.
- **Compression along a Kazhdan pair reaches only restrictions.** Let
  `G ↷ (X, μ)` be p.m.p., `Γ ≤ G` and `t ∈ G` with `tΓt^(-1) ≤ Γ`. The map
  `x ↦ t·x` intertwines the `Γ`-action with the `tΓt^(-1)`-action along
  `γ ↦ tγt^(-1)`, so `h_Γ(X) = h_(tΓt^(-1))(X)`.
  - For finite index `m = |Γ : tΓt^(-1)| ≥ 2`, Seward arXiv:1602.06680v2
    Lemma 8.1 gives only `h_(tΓt^(-1))(X) ≤ m·h_Γ(X)`, which is vacuous here.
  - The reverse inequality is the subgroup formula. §1 of that paper records it
    as a conjecture: "For non-amenable groups it is unknown, both for sofic and
    Rokhlin entropy". Lemma 8.3 proves it when almost every ergodic component
    splits into `m` components. Under the formula, `h_Γ(X) ∈ {0, ∞}`.
  - The Kun–Thom and Leavitt compressions have infinite index, and there nothing
    follows.
  - In every case `G`-level Rokhlin entropy is bounded only above by the entropy
    of an ergodic restriction, so these constraints do not reach POS.
- **The lamp-invariant factor gives no lower bound.** The Kun–Thom wreaths
  `W = (⊕_(G/Γ) Z/2) ⋊ G` have an infinite amenable normal subgroup `N` of
  lamps and a sofic quotient `G`. A lower bound
  `h^Rok_W(X) ≥ h^Rok_(W/N)(X_N)` through the `N`-invariant factor `X_N` fails
  already for amenable groups:
  - take `W = Z^2` and `N = Z × 0`;
  - take `Y` to be the 2-shift in the second coordinate, with `N` acting
    trivially, and `Z` a free Bernoulli `Z^2`-shift of base entropy `ε < log 2`;
  - then `X = Y × Z` is free and `X_N = Y` has `W/N`-entropy log 2;
  - but `h_W(X) = h_W(Y) + h_W(Z) = 0 + ε`.
  Soficity of the lamp quotient gives nothing through the invariant factor.
- **Orbit-relation invariants give no lower bound (2026-09-12, gk-p-inf-cost).**
  - All nontrivial finite-alphabet Bernoulli shifts over an infinite group are weakly equivalent
    (`nontrivial-bernoulli-shifts-are-weakly-equivalent`, from Abért–Weiss in both directions). So
    cost (for finitely generated groups), fixed price, ℓ²-Betti numbers and every weak-equivalence
    or group invariant take one value on all bases.
  - Their Rokhlin entropy is at most `H(1−p, p) → 0`. So no base-independent lower bound through
    such invariants is positive, on any group (`weak-invariants-give-no-bernoulli-rokhlin-lower-bound`,
    which invalidates `positive-rokhlin-entropy-via-weak-invariant-bounds`).
  - By Seward's Theorem 1.10 a Bernoulli lower bound is a lower bound for `h_sup(G)`. On Kazhdan hosts
    the first-order group invariants are trivial there: infimal cost `1`, and `β^(2)_1 = 0` by
    Gaboriau's inequality.
- **Free subrelations transfer nothing (idea, not landed as a claim).** For nonamenable `G`, the orbit
  relation of the Bernoulli shift `[0,1]^G` contains the orbit relation of a free p.m.p. action of
  `F_2` (Gaboriau–Lyons, *A measurable-group-theoretic solution to von Neumann's problem*, Invent.
  Math. 177 (2009)). `F_2` is sofic, so that subaction has entropy lower bounds. No transfer to
  `h^Rok_G` is known:
  - a `G`-generating partition need not generate along the smaller `F_2`-orbits;
  - the `F_2` generators act through cocycles into `G` with infinitely many values, so recording them
    costs unbounded entropy.
- **Sofic actions and sofic orbit relations are unavailable over nonsofic
  groups (2026-09-12, gottschalk-rokhlin-lower-bound).** Suppose a free action
  is sofic in Păunescu's sense (`paunescu-sofic-action-class-permanence`,
  Definition 1.4). The crossed product then embeds in a matrix ultraproduct
  with `G` in the permutation matrices, and `τ(u_g) = μ(Fix g) = 0` for
  `g != 1`. That is a sofic approximation of `G`. So no free action of a
  nonsofic group is sofic, and entropy theories built on sofic actions or sofic
  orbit relations are undefined over the binary Leavitt unit group and the
  tester host.
- **Weak containment only moves positivity around.** Seward,
  arXiv:1602.06680v2:
  - Lemma 1.1 bounds a weakly containing joining's relative entropy from above
    by the contained one's;
  - Theorem 1.2 is an equality for actions weakly contained in all free actions;
  - the paper says the Bernoulli case "leads to new upper bounds to Rokhlin
    entropy".

  A positive lower bound must enter as an input.
- **Følner counting along amenable Schreier graphs needs right-Følner windows
  in `G`.** Try to bound a partition `α` from below using a Bernoulli factor over
  a coset space `G/H` with Følner sets `F_n`.
  - The counting reads `α`-names over `F̃_n S^-1`, where `F̃_n` lifts `F_n` to `G`
    and `S` is the window of `α`.
  - It gives nearly `log q` only when `|F̃_n S^-1| <= (1+ε)|F̃_n|`.
  - `α`, and hence `S`, is arbitrary, so this needs right-Følner sets for every
    finite `S` in `G`, i.e. `G` amenable.
  - The coset action is also not free, and moving the bound to a free action
    goes through outer entropy, which is again what needs bounding (artifact
    `research/artifacts/rokhlin-lower-bound-mechanisms-2026-09-12.md`, §2.5).
- **The Koopman representation gives necessary conditions only.**
  `koopman-lambda-singular-part-has-zero-rokhlin-entropy` (Seward,
  arXiv:1804.05270v1, Theorem 1.2): entropy lives on the part of the Koopman
  representation not singular with `λ`, and `λ^⊕N` embeds in every
  positive-entropy free ergodic action. The Bernoulli shift passes this test
  whatever its entropy.
- **A nonsofic test case.** `kun-thom-wreath-bernoulli-rokhlin-maximal` asks
  for maximal Bernoulli entropy over a surjunctive Kun–Thom wreath. It would be
  the first lower bound over any nonsofic group. It is open, with its specific
  obstructions recorded there.
- **Invariant layers carry no entropy (ex-rokhlin-lower, 2026-09-12).** In every free action, the sets
  fixed by any infinite subgroup generate a sigma-algebra of zero outer Rokhlin entropy
  (`infinite-subgroup-invariant-information-has-zero-outer-entropy`). The closed span of the fixed vectors is
  singular with `λ`, so Seward's Theorem 1.2 applies. Special cases:
  - factors fixed by an infinite normal subgroup (Alpeev–Seward, Krieger III, Theorem 1.11, imported as
    `alpeev-seward-stabilizer-growth-kills-outer-entropy`);
  - the `Γ`-invariant functions of Kun–Thom Theorem C, the information that separates sofic actions from the
    rest;
  - information fixed by the invisible lamps of the Kun–Thom wreath;
  - generalized Bernoulli shifts over infinite subgroups and affine lamp actions, whenever essentially free.

  Every nonsoficity mechanism in the graph lives on such invariant layers. So a lower bound, or a deficit, has
  to act on the mixing part of an action, where the Koopman data is `λ^⊕N` and blind.
- **What is left.** A lower bound for any nonsofic group needs a counting
  mechanism that is not a sofic approximation. The sources read here
  (arXiv:1501.03367, 1602.06680, 1804.05270, 1805.08279, 0812.2718) derive lower
  bounds only from sofic entropy or from amenability.
- **Information-inequality proofs relativize (sw-050, 2026-09-17).**
  - Fix a group `G`. Every argument that derives `Phi >= c log q` using only the following inputs also applies to a code that sees free side information from any p.m.p. action `Ω`:
    - linear information inequalities;
    - invariance of the joint law;
    - independence of the input;
    - locality of the code;
    - conditional independence of disjoint windows.
  - Such an argument therefore proves `h_G((A^k)^G × Ω | B(Ω)) >= c k log q` for every `Ω`
    (`entropy-profile-proofs-of-bernoulli-maximality-relativize`). For `c = 1` this is the Bernoulli case of Seward's
    direct-product conjecture, for all `Ω` at once.
  - The minimal-window Shannon certificates below are proofs of this kind. So
    `torsion-free-windows-have-minimal-shannon-certificates`, if true, would also give that relative equality for every
    torsion-free group and every action.
  - The concrete test is the Kun–Thom nonsofic action of a residually finite Kazhdan group
    (`kun-thom-nonsofic-action-carries-full-bernoulli-entropy`), where sofic counting is unavailable. A deficit there
    kills every such proof of the flagship.
  - A proof that avoids this barrier must use that `psi` is the same function at every site in a way that joint
    entropies cannot see, for example evaluation on special inputs or finite models.
- **Minimal-window Shannon certificates die on torsion (a-gs-rokhlin-obstruction, 2026-09-17).** This was a census
  of the proof method behind the window normal form `rokhlin-window-transport-is-dominated`, using the
  polymatroid LP of `research/artifacts/shannon-window-certificates-2026-09-17.md`.
  - **Class killed** (`minimal-window-shannon-derivations-miss-rokhlin-domination`, ESTABLISHED by exact rational
    verification). Consider Shannon-type derivations of `Phi >= log q` that use only the configuration's own window: `x` on
    `FE ∪ {1}` and `y` on `F`, with independence, functional dependence and translation invariance.
    - They fail in every group with an element of order 3, 4 or 5.
    - For `E = {1,t,t^2}`, `F = {1,t}` with `t^3 = 1`, a translation-invariant polymatroid on the five window variables
      satisfies every premise and has `Phi = 5/6`. The values at orders 4 and 5 are `7/9` and `4/5`.
    - The inequality is true there (`lambda(F) = 1`), and adding the missing codeword `y_(t^2)` restores LP value 1.
    - Every member of the class dies at the final nonnegative combination of elemental inequalities.
    - So any proof of domination must bring in codewords outside `F`, as the Følner count does, or use non-Shannon or
      nonlinear information.
  - **Torsion-free evidence** (`torsion-free-windows-have-minimal-shannon-certificates`, OPEN).
    - All 140 tested torsion-free configurations (`F_2`, `Z`, `Z^2`, `H_3(Z)`, `|V| <= 13`) certify on their minimal window.
    - The same windows read in `Z` certify where `Z/3`, `Z/4` and `Z/5` fail.
    - If this held for all torsion-free groups, Bernoulli maximality would follow for every torsion-free group, including the torsion-free nonsofic hosts. By `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, their surjunctivity would follow too.
    - This root would not follow, since Theorem 1.11 passes through `P × G` with `P` locally finite, which has torsion.
  - **Not tried here.** Non-Shannon inequalities on the torsion fakes; a torsion-free pattern with LP `< 1`.
- **Past-conditioned domination (swarm-0917-w5-pull-gs-4, 2026-09-17, OPEN, no class kill).** Scripts are in
  `experiments/shannon-ordered-certificates-2026-09-17/`.
  - **Reduction.** Let `G` be left-orderable. Suppose `D: I(x_1 ; y_F | x_{<1}) <= H(y_1)` holds for every finite
    `F` and every code. Then `Phi = H(y_1) + H(x_1|y_F) >= I + (log q - I) = log q`, because
    `H(x_1|y_F) >= H(x_1|x_{<1}) - I(x_1;y_F|x_{<1})`. So `D` would give Bernoulli maximality for every
    left-orderable group.
  - **The conditioning must be past-type.** Conditioning on all other coordinates fails. With AND codes and `m = 3`,
    `I = 0.578 > h(1/8) = 0.544`.
  - **Invariant fakes pass to overgroups.** A `H`-invariant fake extends to `G >= H` as the independent product over
    left cosets. So the torsion kill above covers every group with an element of order 3, 4 or 5. Left-orderable
    groups are torsion-free, so `D` is not touched by it.
  - **Linear codes.** `D` holds on bi-orderable groups whenever the code block at `max E` has full row rank. The
    unique maximal product `max S * max E` gives a triangular rank count. A violation needs
    `beta < rank L < k`, where `beta` is the rank of the combined leading blocks.
    - Script `left_order_linear_domination.py`: random and structured rank-deficient codes over `F_2` and `F_3`,
      tested on `Z` and on `F_2` in the Magnus order.
    - For `F_2` the windows were `E in {1ab, 1a(ab), 1a(Ab), 1ab(ab)}` with `F = ball(2)`.
    - Worst gap was `I - H(y_1) = 0` in every case, with no violation.
    - This case is not new. It follows from stable finiteness of `K[F_2]`, which is a fir.
  - **Ordered termwise split.** The stronger inequality `I(x_1;y_F) <= sum_{readers f} I(x_1; y_f | x_{P_f})`
    implies `D`.
    - It has a hand proof on `Z` for interval `E` with `F = -E`: comparing total correlations after conditioning on
      the past.
    - It is Shannon-provable on the window for `F = -E` in every tested case.
    - It is not provable for `E = {0,1,2}`, `F = {-1,0}`: window LP `-0.5`.
    - It is false for codes that are not readers.
    So it is not a general mechanism.
  - **Wider `Z` census.** `scan_z_wide.txt`: `|E| in {3,4}`, `|F| <= 4`, at least two readers, `n <= 12`. Every
    configuration completed so far has LP exactly `1`, and no torsion-free fake was found.
  - **Where it stops.** The remaining case is nonlinear codes on `F_2` under a left order. The window has 35 or more
    sites, so exhaustive `q = 2` evaluation is infeasible, and the window LP does not see the order. Neither a proof
    nor a counterexample to `D` was obtained.
- **Co-Hopfian conjugacy invariants are pre-empted (swarm-0917-w5-pull-gs-3, reframing, 2026-09-17).** Idea: replace entropy with a
  conjugacy invariant of `G`-subshifts that is monotone under inclusion and strictly drops on a proper subshift of `A^G`. Candidates
  were the clopen type semigroup and `K_0` of `C(X) ⋊ G`. The lane dies at its first step, and the death is already recorded in
  `gottschalk-surjunctivity-conjecture`.
  - An injective automaton `tau` induces the unital pullback endomorphism `f -> f o tau` of `C(X)`, which extends to the crossed
    product. Its kernel is the ideal of functions that vanish on `tau X`. So a strict drop is exactly non-injectivity of this
    endomorphism, and any "Hopfian crossed product" invariant restates the goal.
  - The states on `K_0` (and on the type semigroup) are the invariant measures. Any finite additive dimension that is monotone
    under `Phi_tau` is invariant: apply monotonicity to `1 - e`. That is the operator-algebraic dimension lane (sw-003). Its
    diagonal sector is the goal-equivalent `injective-measure-preserving-ca-is-surjective`. Affine self-embeddings of the
    Poulsen or Bauer simplex make index-type readings blind.
  - What is not covered: non-additive, non-cancellative type-semigroup data that is not seen by states. No candidate was found
    that is not a restatement of the lattice of closed invariant subsets, so nothing was landed.
- **Torsion window fakes are entropic (swarm-0917-w5-pull-gs-1, 2026-09-17).** This follows up the non-Shannon gap above.
  - **Established** (`torsion-window-fakes-are-realized-by-f2-linear-codes`, exact integer verification). The `Z/3` fake
    `Phi = 5/6` is the entropy vector of two rank-5 `F_2`-linear maps on three independent uniform `F_2^6` sites. So no
    information inequality of any kind, Shannon or not, derives `Phi >= 1` from the entropy premises (I), (D), (T) in a group
    with an element of order 3.
  - **Computation.** Adding every Zhang–Yeung instance leaves the LP values at `5/6`, `7/9`, `4/5` for orders 3, 4, 5.
  - **Where it dies.** (T) equates entropies of translates, not laws. The realization uses non-equivariant codewords
    (`W_1 ≠ W_0 ∘ shift`). Invariance in law forces the orbit codeword `y_(t^2)`, and then the LP has value 1. A surviving
    local proof must use invariance in distribution, or codewords outside `F`.
  - **Open.** Whether the `Z/4`, `Z/5`, Klein and `D_inf` fakes are entropic. A simulated-annealing search for `F_2`-linear
    realizations (`experiments/entropic-window-fakes-2026-09-17/linrep.c`) found `Z/3` quickly and had not found the
    others at the time of writing.
- **Window fakes on `Z/4`, `Z/5`, `Z/7`, Klein and `D_inf` are entropic (swarm-0917-w6-w6-gs-pull, 2026-09-18).** This closes the open item of the previous attempt.
  - **Established** (`window-fakes-on-z4-z5-z7-klein-and-dinf-are-entropic`). Exact `F_2`-linear realizations satisfy (I), (D), (T):
    - `Z/4` and `(Z/2)^2`: `Phi = 85/107`;
    - `Z/5`: `Phi = 4/5`, ten one-bit atoms, hand-checkable;
    - `D_inf`: `Phi = 52/55`;
    - `Z/7`: `Phi = 1479/1712`.
    `verify_linear.py` re-verified the first four on the concatenated codes, ALL EXACT.
  - **Class killed.** No derivation of `Phi >= 1` from (I), (D), (T) plus any valid information inequality exists on minimal windows in any group with an element of order divisible by 3, 4, 5 or 7, or with two distinct involutions of even or infinite product. On these hosts non-Shannon information does not rescue the method.
  - **Method.** The linear-atom LP takes convex combinations of rank vectors of one-bit linear codes and imposes (T) only on the mixture. A rational optimum is a direct sum of copies, hence entropic. Annealing a single code had failed on these hosts; the LP finds the fakes in minutes.
  - **Where it dies.** No atom is translation invariant; only the mixture satisfies (T), in entropy and not in law. A surviving local proof must use invariance in distribution, or codewords outside `F`.
  - **Open.** Whether the Shannon values `7/9`, `7/8`, `5/6` are themselves entropic. The atom LP was restricted to codeword subspaces of dimension at most 1.
- **Distribution-level certificates die at Bowen and Seward realisations (swarm-0917-w7-w7-gs-pull, stability-approximation, 2026-09-18).** This transplants the Hilbert--Schmidt (hyperlinear) microstate idea at the level of its leading-order dimension.
  - **Established** (`distribution-certificates-are-shannon-monotone`, with the new import `bowen-every-countably-infinite-group-is-almost-ornstein`). Over every countably infinite `G`, let `f` be a functional on generator distributions with `f(dist α) >= f(p)` for every generating partition `α` of `B(p)`. Then `f(q) >= f(p)` whenever `H(q) > H(p)`, by Seward's prescribed-distribution generators. And `f(q) = f(p)` on each Shannon level set of vectors with at least three atoms, by Bowen's almost-Ornstein theorem. If `f` is non-constant, then `h^Rok(B(p)) >= H(q) > 0` for some `p`, `q`, which is POS for `G`.
  - **Class killed.** On every group, including a hypothetical zero-supremum group, the following certify nothing:
    - the HS commuting-projection dimension `1 - Σ q_i^2`, which is the collision functional;
    - all Rényi entropies `H_α` for `α ≠ 1`, including the support count and the min-entropy;
    - all Tsallis entropies `S_α` for `α ≠ 1`.

    Explicit witness: the base `(a, a, 1-2a)` with `H = 1.5` bits has a generator of distribution `(1/2, 1/4, 1/4)`, and its value `1 - Σ^2` drops from `0.631` to `0.625`.
  - **Invariant, and where it dies.** The invariant is the one-site distribution of the generator. Every member dies at the realisation step, where the time-zero partition of an equal-entropy (or larger-entropy) base is transported into `B(p)`. Together with `hs-commutative-microstate-bernoulli-entropy-is-base-blind` (the volume is `+∞`), both natural HS quantities fail.
  - **What survives.** Statistics of joint windows (see the cluster and minimal-window kills), and counts whose exponent is Shannon entropy itself, i.e. multinomial or diagonal (sofic-type) counts. For these, soundness is at least as strong as the lower bound they give.
