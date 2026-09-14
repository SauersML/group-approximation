# Gottschalk surjunctivity: round-two ideas

Lane `ideas-gottschalk-2`, 2026-09-14, main at `86572ea5c`. This artifact changes no existing node. Everything here is
unreviewed.

## 0. Verdict

- **The region is saturated.** About 945 files on main touch surjunctivity. I examined fourteen routes and one
  critical-path check against the landed firewalls.
  - Eleven are dead: they either collapse onto a landed firewall or restate folklore.
  - Two were executed and landed as new claims (Section 3).
  - Two survive as open questions (Section 4).
- **Landed claims (unreviewed):**
  - `nonamenable-groups-carry-arrow-shift-strict-automata`. Every nonamenable group carries a strict automaton, fibred
    over a nonempty arrow shift of finite type. That shift has no finite orbits, so no equivariant map from a full shift
    reaches it.
  - `linear-strict-pairs-are-transposes-of-post-surjective-automata`. A linear automaton is injective and not
    surjective iff its transpose is post-surjective and not pre-injective. So a linear Gottschalk witness is also a
    linear counterexample to the dual surjunctivity conjecture.
- **Gottschalk's conjecture stays OPEN in both directions.** No famous problem is decided here.

## 1. What a new idea must survive

These are the landed filters I checked every idea against.

- **Soficity and permanence.**
  - Sofic groups are surjunctive.
  - `gottschalk-counterexamples-lie-outside-the-permanence-closure`: no finitely presented infinite simple nonsofic
    group lies in the closure `S*`.
- **Counting on finite models collapses to soficity.**
  - `separating-repetitive-amenable-schreier-families-force-soficity`
  - `partial-schreier-completion-preserves-sofic-loss`
  - the dead route `weakly-sofic-surjunctivity-via-hamming-transport`
- **Universal closure.**
  - `surjunctivity-is-axiomatized-by-rectangle-clauses`
  - `gottschalk-surjunctivity-fixed-two-generator-tester`
  - `gottschalk-reduces-to-fg-simple-kazhdan-groups`
- **Rokhlin entropy.** The only known lower bound is sofic entropy
  (`infinite-rokhlin-supremum-forces-surjunctivity` is an import). Relevant nodes:
  - `alpeev-seward-stabilizer-growth-kills-outer-entropy` and the Ornstein–Weiss decoder nodes;
  - finite kernels: `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`,
    `bernoulli-lifts-across-finite-kernels-force-virtual-splitting`.
- **The linear wall.**
  - `stable-finiteness-failure-refutes-surjunctivity`
  - `formalizable-pairs-reduce-surjunctivity-to-kaplansky`
  - `infinite-field-polynomial-strict-pairs-need-kaplansky-failure`
- **Quantization, tables, decoders and transport.**
  - `split-ca-quantization-has-sharp-defect`
  - `strict-pairs-transfer-to-table-realizations`
  - `cubulated-hyperbolic-table-cores-carry-no-strict-pair`
  - `split-decoders-have-generic-cantor-fibers`
  - `injective-ca-random-order-transport-identity`

## 2. The ideas

Each entry gives the mechanism, the kill test, and the verdict.

**I1. Schreier-periodic density.**
- **Mechanism.** Use configurations fixed by non-normal subgroups `H`, with amenable Schreier graphs `H\G` or
  invariant-random-subgroup models, instead of finite quotients.
- **Kill test.** Surjectivity on `Fix_H` must reach every pattern. So the window has to be injective at a positive
  fraction of model points. Elek–Szabó amplification then makes `G` sofic, which is the landed Schreier firewall.
- **Verdict. DEAD.**

**I2. Twisted periodic points for finite central extensions.**
- **Mechanism.** For `N` finite central in `G` with `Q = G/N` residually finite, `A^G = (A^N)^Q` with a cocycle twist.
  The idea is to untwist by carrying the gauge field `q -> z(q, .)` as an extra track.
- **Kill test.**
  - For Deligne-type covers, every finite-index subgroup contains `N`, so every periodic configuration is
    `N`-invariant.
  - The untwisted pair automaton would have to be injective for every gauge field, and it need not be.
  - The team already carries this as `finite-kernel-*`.
- **Verdict. DEAD.**

**I3. Multiset coset factor with N-saturation.**
- **Mechanism.** Let `N` be finite normal and `X = B^G` uniform Bernoulli.
  - The map `y(qN) = {multiset of x on qN}` is a `G`-equivariant factor onto a `G/N`-Bernoulli shift. The multiset base
    has entropy about `|N| log|B| - log |N|!`.
  - For any partition `P`, the finite join over `N` of the translates of `P` descends to `X/N`. This gives
    `h_G(Y ⊆ X) >= h_(G/N)(Y ⊆ X/N) / |N|`.
  - With `infinite-rokhlin-supremum-forces-surjunctivity`, a full lower bound would make every finite extension of a
    sofic group surjunctive, including Deligne's triple cover.
- **Kill test.**
  - The missing input is a lower bound for the outer Rokhlin entropy of a Bernoulli factor inside the twisted quotient
    `X/N`.
  - Ornstein–Weiss factor maps show that outer entropy of a Bernoulli factor can fall below its base entropy.
  - The only lower-bound method is sofic models, and the twisted quotient `X/N` has none unless the cover itself is
    approximable.
  - Same difficulty as `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`.
- **Verdict. DEAD as a route.** The two formulas are recorded here only.

**I4. The paradoxical arrow hotel.**
- **Mechanism.** On a nonamenable group, a bounded-displacement surjection `f` with two preimages everywhere gives
  `x -> x∘f`, which is injective and not surjective.
- **Executed (Section 3.1).** The arrow fields form a nonempty shift of finite type `X_S`. The hotel map is strict on
  every fibre. `X_S` has no finite orbits, so no equivariant map from any full shift reaches it.
- **What it formalizes.** The "design wall" becomes a precise interface. A counterexample must synthesize an arrow
  field from the data, and that field must fail on every symmetric configuration. Free groups are sofic, so the defect
  handling must use nonsofic relations.
- **Verdict. SURVIVES as a design interface.**

**I5. The dual surjunctivity bridge.**
- **Mechanism.** Capobianco–Kari–Taati ask whether every post-surjective automaton over every group is pre-injective.
  Attribution not re-pinned: the arXiv API returned HTTP 429 to this lane.
- **Executed (Section 3.2).** In the linear case the two conjectures fail together, exactly by transposition.
- **Kill test for the nonlinear bridge.** Given a strict `tau` with left inverse `sigma`, one would choose `sigma`'s
  rule off the image so that `sigma` is post-surjective and not pre-injective.
  - Post-surjectivity holds at points of the image (lift the modification through `tau`).
  - Configurations carrying Garden-of-Eden patterns are the obstruction: `sigma` must be locally onto there.
- **Verdict. SURVIVES as an open question.**

**I6. Upgrading Myhill failure.**
- **Mechanism.** Bartholdi–Kielak give pre-injective, non-surjective linear automata on every nonamenable group
  (attribution not re-pinned). The idea is to upgrade pre-injective to injective.
- **Kill test.**
  - The upgrade removes infinite-support kernel vectors, and that is exactly stable-finiteness failure.
  - Myhill failures already exist on free groups, which are sofic and so stably finite. The upgrade therefore needs
    nonsofic input.
  - This lands back on the linear wall.
- **Verdict. DEAD.**

**I7. Hyperlinear implies surjunctive.**
- **Mechanism.** If hyperlinear groups were surjunctive, a Gottschalk counterexample would be a non-hyperlinear group.
- **Kill test.**
  - Unitary models carry no pattern counts.
  - In a rank-metric model the relations hold on a subspace of codimension `εd`. That subspace holds only a `p^(-εd)`
    fraction of vectors, so almost no sites are good.
  - `weakly-sofic-groups-are-surjunctive` and `linear-sofic-groups-are-surjunctive` are OPEN and sit below this idea.
- **Verdict. DEAD as a route.**

**I8. Automatic reversibility of quantum automata.**
- **Mechanism.** Schumacher–Werner-type automatic reversibility over all groups, through the unique trace and the Jones
  index of `G`-invariant subfactors of `⊗_G M_A`.
- **Kill test.** A strict classical automaton induces no local `*`-endomorphism of the quasi-local algebra, because its
  range projection is nonlocal (`split-ca-quantization-has-sharp-defect`).
- **Verdict. DEAD for Gottschalk.** The quantum question is separate.

**I9. Algebraic deformation in the style of Ax–Grothendieck.**
- **Mechanism.** Extend a finite strict pair to polynomial maps over an algebraically closed field.
- **Kill test.** `infinite-field-polynomial-strict-pairs-need-kaplansky-failure`. In characteristic zero, Kaplansky's
  theorem forbids such an extension.
- **Verdict. DEAD.**

**I10. Kolmogorov complexity of configurations.**
- **Mechanism.** For hosts with solvable word problem, compare the complexity of `x` and `tau(x)` on balls.
- **Kill test.** The inequality obtained is `|B_n| <= (1-δ)|B_(n+r)|`. That is true on nonamenable groups: it is the
  entropy count again.
- **Verdict. DEAD.**

**I11. Rigidity of invariant measures.**
- **Mechanism.** Use property (T) rigidity: the Glasner–Weiss Bauer simplex, or Connes–Weiss strong ergodicity.
- **Kill test.** `tau` transports Bernoulli measures to singular measures on the image. Closedness of the ergodic
  measures gives no contradiction.
- **Verdict. DEAD.**

**I12. A filter from limits of hyperbolic groups.**
- **Mechanism.** Surjunctivity is closed in the space of marked groups. So if all hyperbolic groups are surjunctive,
  so are their limits, including Tarski monsters and free Burnside groups of large odd exponent.
- **Kill test.**
  - This is a corollary of rectangle-clause closure.
  - The table side is covered by `cubulated-hyperbolic-table-cores-carry-no-strict-pair`.
  - Finitely presented simple non-hyperbolic hosts are not hyperbolic-realizable: a partial embedding of a relator
    ball is an embedding.
- **Verdict. DEAD as new content.**

**I13. A Boone–Higman bridge.**
- **Mechanism.** Realize strict tables on groups with solvable word problem. Under Boone–Higman, embed those in finitely
  presented simple groups.
- **Kill test.**
  - Canonical table groups are finitely presented, but realizations with solvable word problem are not guaranteed.
  - The literature reportedly has finitely presented groups whose nontrivial quotients all have unsolvable word
    problem. This lane did not pin that.
  - The fixed tester host is already finitely presented.
- **Verdict. DEAD unless that literature claim fails.**

**I14. Mass transport and information conservation.**
- **Kill test.** Already landed: `injective-ca-random-order-transport-identity`. Its domination is OPEN.
- **Verdict. COVERED.**

**I15. Critical path: soficity of `Γ_4 = <S4>` and `Γ_5 = <S4, x_23(1)>`.**
- **Mechanism.**
  - Under the code-`(0,1)` isomorphism, `Γ_4 <= EL_2(J_(F_3))` acts by banded Toeplitz operators on
    `F_3^(N) ⊕ F_3^(N)`.
  - Its kernel is finitary, hence locally finite. Its quotient is `SL_2(F_3[ζ, ζ^(-1)])`.
  - By the synthesis, section 4.1, soficity of `Γ_5` refutes `four-transvections-and-x23-force-defect-vanishing`.
- **Kill test.**
  - Truncations are rank-metric models, and finitary kernel elements vanish in normalized rank.
  - Permutation models on `F_3^L` pay Hamming error near 1 from rank-`O(1)` boundary terms.
  - Soficity of locally-finite-by-sofic extensions is open in general.
  - So a decision needs structure specific to `Γ_5`.
- **Verdict. SURVIVES.** It decides the team's top lead either way.

## 3. Executed survivors

### 3.1 The arrow hotel (landed)

**Claim.** `nonamenable-groups-carry-arrow-shift-strict-automata`; route `arrow-shift-strict-automata-proof`.

- **Theorem.** For every countable nonamenable group `G` there is a finite `S` containing `e` such that:
  - the arrow shift `X_S = {φ in S^G : every h has at least two g with gφ(g) = h}` is a nonempty shift of finite type;
  - `Φ(φ, x) = (φ, x∘f_φ)` with `f_φ(g) = gφ(g)` is a block map on `X_S × A^G` that is injective and not surjective on
    every fibre;
  - `X_S` has no point with finite orbit;
  - consequently there is no `G`-equivariant map, continuous or not, from any full shift into `X_S`.
- **Converse.** If `G` is amenable, then `X_S` is empty for every finite `S`.
- **Proof ingredients.**
  - Følner's criterion gives `|FS| >= 2|F|`.
  - Hall's theorem for families of finite sets gives the two-fold matching.
  - Periodic arrow fields would induce a map on a finite coset space with two preimages everywhere, which is
    impossible.
- **Consequence.** Every strict automaton on a full shift that works hotel-style has to compute an arrow field from the
  data. That computation fails at every symmetric configuration. So the landed decoder-fibre and table filters are the
  only places the defect can be absorbed.

### 3.2 Linear transposition (landed)

**Claim.** `linear-strict-pairs-are-transposes-of-post-surjective-automata`; route
`linear-strict-transpose-duality-proof`.

- **Setup.** Let `k` be any field and `tau(x)(g) = Σ_m x(gm) A_m` a linear automaton on `(k^n)^G`. Its transpose is
  `tau^T(x)(g) = Σ_m x(g m^(-1)) A_m^T`.
- **Theorem.** `tau` is injective and not surjective iff `tau^T` is post-surjective and not pre-injective.
- **Proof.** Configurations are the algebraic dual of `k[G]^n`, and `tau` is the adjoint of the restriction of
  `tau^T` to finite support. Linear duality exchanges injective with surjective. By linearity, pre-injectivity and
  post-surjectivity of `tau^T` are injectivity and surjectivity on finite support.
- **Consequence.** Every one-sided inverse over a finite field refutes both conjectures at once: Gottschalk (landed
  criterion) and the linear case of dual surjunctivity.

## 4. Ranked survivors and the next deep lane

1. **I15:** decide soficity of `Γ_4` and `Γ_5`. This is on the critical path of the ternary Leavitt root, which would
   refute Gottschalk.
2. **I5:** the nonlinear relation between Gottschalk and dual surjunctivity. Does a strict pair yield a post-surjective,
   non-pre-injective automaton on the same group or on `G × Z`?
3. **I4:** hotel synthesis on the Leavitt hosts and on V. Compute arrow fields from data along the Cantor action, and
   find where the defects can be absorbed.

**Single best next deep lane: I15.** Its answer either refutes the team's top lead or feeds it.
