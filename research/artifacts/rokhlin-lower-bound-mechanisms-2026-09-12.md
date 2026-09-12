# Rokhlin entropy lower bounds without sofic models: a mechanism audit

Lane `gottschalk-rokhlin-lower-bound`, 2026-09-12.

**Target.** A lower bound for the Rokhlin entropy of some free ergodic p.m.p.
action of `U = L_(F_2)(1,2)^x` or of the tester host `U_*`, obtained without
sofic entropy. The relevant claims are
`leavitt-unit-group-has-positive-rokhlin-entropy-action` and
`tester-host-has-positive-rokhlin-entropy-action`. A positive answer for `U`
would make `U` surjunctive and `K[U]` directly finite
(`positive-rokhlin-entropy-makes-leavitt-units-surjunctive`).

**Result.** No mechanism was found. This note records:
- the sources read from the PDFs;
- each mechanism tested, and exactly where it dies;
- the most tractable nonsofic test case, opened as
  `kun-thom-wreath-bernoulli-rokhlin-maximal`.

## 1. Sources read from the PDFs

The text was extracted on MSI on 2026-09-12. Spacing lost in extraction is
restored in the quotes below.

### Seward, *The Koopman representation and positive Rokhlin entropy*, arXiv:1804.05270v1

> **Theorem 1.2.** Let G ↷ (X, μ) be a free p.m.p. action, and let
> ρ : G → U(L²(X, μ)) be the corresponding Koopman representation. Also let
> λ : G → U(ℓ²(G)) be the left-regular representation. If H is a ρ(G)-invariant
> closed subspace of L²(X, μ) and ρ|_H is singular with λ, then
> h_G(σ-alg(H)) = 0.

> **Corollary 1.3.** Let G be a countably infinite group, let π : G → O(H) be an
> orthogonal representation on a real separable Hilbert space H, and let
> λ_R : G → O(ℓ²(G; R)) be the real left-regular representation of G. Suppose
> that π is singular with λ_R. Then the Gaussian action G ↷ (X_π, μ_π) induced
> by π satisfies h_G(X_π, μ_π) = 0.

The text before Corollary 1.5: "since the Koopman representation of any
Bernoulli shift is isomorphic to λ^⊕N, it follows from Theorem 1.1 that λ^⊕N
embeds into the Koopman representation of any free ergodic p.m.p. action with
positive Rokhlin entropy."

Theorem 1.1 is cited there from Seward's earlier work, and it is the
Bernoulli-factor theorem for positive-entropy actions. The theorem gives a
necessary condition and never a lower bound.

### Seward, *Weak containment and Rokhlin entropy*, arXiv:1602.06680v2

> **Lemma 1.1.** Let G ↷ (X × Y, λ) and G ↷ (X × Z, ρ) be joinings with an
> aperiodic action G ↷ (X, μ). Let F be a G-invariant sub-σ-algebra of X. If
> G ↷ (X × Z, ρ) weakly contains G ↷ (X × Y, λ) as joinings with G ↷ (X, μ),
> then h_G(X × Z, ρ | F ∨ B(Z)) ≤ h_G(X × Y, λ | F ∨ B(Y)).

> **Theorem 1.2.** Let G be a countably infinite group, let G ↷ (X, μ) be a free
> p.m.p. action, and let F be a G-invariant sub-σ-algebra. If G ↷ (Y, ν) is a
> p.m.p. action which is weakly contained in all free p.m.p. actions of G then
> h_G(X, μ | F) = h_G(X × Y, μ × ν | F ∨ B(Y)).

On Corollary 1.3 of that paper, which is the Bernoulli case of Theorem 1.2: "The
value of this corollary is that the right-hand side is a bit more manageable and
leads to new upper bounds to Rokhlin entropy (and thus upper bounds to sofic
entropy as well)." Theorems 1.4 and 1.5 are upper bounds.

### Already on main, from earlier lanes

- arXiv:1501.03367, introduction: every known lower bound runs through sofic
  entropy.
- arXiv:0812.2718: over groups containing F_2, all nontrivial Bernoulli shifts
  are weakly isomorphic.

## 2. Mechanisms tested

1. **Sofic entropy.** Needs a sofic approximation of `G`. `U` and `U_*` have none.

2. **Sofic actions and sofic orbit relations.** Suppose a free action is sofic
   in Păunescu's sense (arXiv:1002.0605v5, Definition 1.4, imported as
   `paunescu-sofic-action-class-permanence`). Then `L^∞(X) ⋊ G` embeds in a
   matrix ultraproduct with `G` in the permutation matrices, trace-preservingly.
   - For `g != 1`, `τ(u_g) = μ(Fix g) = 0`. So the permutations `σ(g)` have
     vanishing fixed-point proportion, and they give sofic approximations of
     `G`.
   - So no free action of a nonsofic group is sofic. For free actions this is
     the same as saying the orbit relation is sofic.
   - Entropy theories built on sofic actions or sofic relations are therefore
     undefined over `U` and `U_*`.

3. **Weak containment.** Every inequality in arXiv:1602.06680 is one of three
   things:
   - it bounds a weakly containing joining from above by the joining it contains
     (Lemma 1.1);
   - it is an equality under containment in all free actions (Theorem 1.2);
   - it is an explicit upper bound (Theorems 1.4, 1.5).

   A positive lower bound has to enter as an input. Weak containment can move
   positivity from one action to another. It cannot create it.

4. **Koopman representation.** arXiv:1804.05270 Theorem 1.2 says entropy lives
   on the part of the Koopman representation that is not singular with λ.
   - It excludes Gaussian constructions from λ-singular representations
     (Corollary 1.3).
   - The uniform Bernoulli shift over any countably infinite group has Koopman
     representation λ^⊕N on the orthocomplement of the constants, so it passes
     the test whatever its entropy. This matches the Koopman-blindness bullet
     on `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`.

5. **Følner counting along amenable Schreier graphs.** Let `G` act on a coset
   space `Ω = G/H` whose Schreier graph has Følner sets `F_n`. Try to bound the
   entropy of a partition `α` from below using the uniform Bernoulli factor
   `A^Ω`.
   - Up to error ε, the coordinate `x(h ω_0)` is a function of the `α`-names at
     `h s^-1 x` for `s` in a finite window `S` chosen by `α`.
   - So `x|_(F_n)` is read off the `α`-names over `T = F̃_n S^-1`, where `F̃_n`
     lifts `F_n` to `G`.
   - The count gives `H(α) >= (1-ε) log q · |F_n| / |T|`. This is near `log q`
     only when `|F̃_n S^-1| <= (1+ε)|F̃_n|`, i.e. only for right-Følner sets for
     `S` in `G`.
   - `α` is arbitrary, so `S` is arbitrary, and right-Følner sets for every
     finite `S` exist exactly when `G` is amenable.
   - Also, the coset action is not free. Transferring a bound to a free action
     goes through outer entropy, which is exactly the quantity to be bounded.

6. **Restriction, co-induction, factor maps.** These give upper bounds only.
   They are recorded on `leavitt-unit-group-has-positive-rokhlin-entropy-action`
   and on `every-group-has-positive-rokhlin-entropy-action`.

7. **Finitary witnesses.** A deficit is witnessed by one finite configuration
   (`bernoulli-rokhlin-deficit-has-a-finitary-witness`), and every witness folds
   on a sofic-invisible element
   (`sofic-radical-localizes-bernoulli-deficit-witnesses`).
   - The Gromov–Weiss count proves the inequality on every configuration with
     no such fold, and on nothing else.
   - Over a simple nonsofic host like `U`, the radical is the whole group, so
     the localization gives no constraint.

## 3. The most tractable nonsofic test case

Let `Γ < G` be a Kun–Thom Theorem E pair and `W = (Z/2) wr_(G/Γ) G`.

- **Why it is a good test case.** `W` is nonsofic (`kun-thom-nonsofic-wreath`)
  and surjunctive (`kun-thom-nonsofic-wreaths-are-surjunctive`, reviewed). So
  the strict-automaton obstruction
  (`strict-automaton-lowers-bernoulli-rokhlin-entropy`) does not apply.
- **Localization.** `W -> G` is a sofic quotient. By Corollary 3 of
  `research/artifacts/bernoulli-deficit-witness-localization-2026-09-12.md`,
  every witness has two points in one lamp coset, differing by a sofic-invisible
  lamp configuration.
- **Finite quotients.** Each finite-index normal `Δ ◁ G` gives a homomorphism
  `W -> (Z/2) wr_(G/ΓΔ) (G/Δ)`, by summing lamps over the fibers of
  `G/Γ -> G/ΓΔ`. The G-action descends, and fiber sums are equivariant.
  - These maps separate a finite subset of `W` once `Δ` separates its G-parts
    and the finitely many cosets in its lamp supports.
  - If `Γ` were closed in the profinite topology, every finite set of cosets
    could be separated. Then `W` would be residually finite, hence sofic.
  - So `Γ` is not profinitely closed. Exact finite models of all witness
    patterns do not exist. The same remark appears in
    `research/artifacts/determinant-conjecture-serre-class-2026-09-11.md`.
- **Lamp-invariant factor.** That route fails already over `Z²`; see the Attempts
  on `every-group-has-positive-rokhlin-entropy-action`.
- **Peeling.** The surjunctivity proof for `W` transplants injective automata
  along bijections and uses no counting. No entropy analogue is known. The
  transplant is a factor map, and Rokhlin entropy is not monotone under factor
  maps over groups containing `F_2`.

A lower bound over `W` would be the first Rokhlin entropy lower bound over any
nonsofic group. It would not by itself reach `U` or `U_*`: `W` has no
centralized self-copy structure of the kind used in
`rokhlin-supremum-dichotomy-with-centralized-self-copies`, and no container
reduction is known from `U` to `W`.

## 4. Status

Nothing is established toward a lower bound. What landed:
- the Koopman vanishing theorem, imported as
  `koopman-lambda-singular-part-has-zero-rokhlin-entropy`;
- the test case, opened as `kun-thom-wreath-bernoulli-rokhlin-maximal`, with its
  specialization route from `bernoulli-rokhlin-entropy-maximal-for-every-group`;
- Attempts bullets for mechanisms 2, 3 and 5, added to
  `every-group-has-positive-rokhlin-entropy-action`.

`leavitt-unit-group-has-positive-rokhlin-entropy-action`,
`tester-host-has-positive-rokhlin-entropy-action` and the new test case stay
OPEN.
