# Swarm attack on fpbs-bounded-cost-fg-torsion-quotient-price-one (2026-09-16)

Agent lane: `swarm-fpbs-bounded-cost-fg-torsion-q`. The target
`fpbs-bounded-cost-fg-torsion-quotient-price-one` (called (T') below) was
locked for the duration of the attack. Nothing was committed.

## 1. Setup

(T'): `N ◁ Gamma` infinite; every essentially free p.m.p. action of `N` has
cost at most `K < infinity` (hypothesis (H)); `Q = Gamma/N` is infinite,
finitely generated and torsion; the outer kernel `Q_0 = ker(Q -> Out(N))`
contains no infinite amenable subgroup. Conclusion: `Gamma` has fixed price
one.

(T') contains `fpbs-burnside-upper-cost-one` (free Burnside groups of large odd
exponent) through `fpbs-burnside-upper-cost-one-via-fg-torsion-quotient`. A
proof of (T') would give fixed price one for those Burnside groups, which is
open (only infimal cost one is known, arXiv:2608.20472). A counterexample
would be a group without fixed price one, which is not known to exist. So the
target itself was not expected to fall; the aim was the most useful sound
reduction.

## 2. What was proved

All proofs are written out in
`research/artifacts/fpbs-infinite-centralizer-price-one-2026-09-16.md`. They
were checked by hand only, and nothing is formally verified. The imports are
Gaboriau's induction formula, Khezeli's product theorem and the repo's
wq-normal lifting lemma.

### 2.1 Lifting across a finite normal kernel (Lemma A)

Node: `fpbs-finite-normal-quotient-lifts-price-one`, with route `-proof`.

**Statement.** If `F ◁ Gamma` is finite and `Gamma/F` has fixed price one,
then `Gamma` has fixed price one.

**Quantitative form.** Every free p.m.p. action of `Gamma` on `X` gives a free
p.m.p. action of `Gamma/F` on a Borel fundamental domain `D` for `F`. For it,
`C(R_Gamma) - 1 = (C(R_{Gamma/F} on D) - 1)/|F|`.

**Proof.**
- Take `D = {x : tau(x) < tau(fx) for all f != e}` for a Borel injection
  `tau`, and let `r` be the retraction onto `D`.
- Define `q.x = r(gamma x)`. This is well defined and an action because `F` is
  normal. It is measure preserving piecewise, and free because the
  `Gamma`-action is free.
- Its orbit relation is `R_Gamma|D`, so the induction formula gives the
  quantitative form.

**Scope.** The converse, from `Gamma` to `Gamma/F`, is not claimed. It would
need lifting arbitrary `Gamma/F`-actions (compare
`bernoulli-lifts-across-finite-kernels-force-virtual-splitting`).

### 2.2 Normal criterion, action-wise (Lemma B)

**Statement.** If `N ◁ Lambda` is infinite, then every free action of `Lambda`
satisfies `C(R_Lambda) <= C(R_N)`. So a uniform cost bound (H) passes from `N`
to every `Lambda` with `N ◁ Lambda`.

**Proof.** Add each coset representative `gamma_j` on a complete section of
`R_N` of measure at most `eps 2^-j`. Lemma B.0 of the artifact constructs small
complete sections through a Borel colouring and a greedy maximal independent
set.

**Where it lives.** This is Gaboriau's Critère VI.24 (2). It is written inline
in the artifact (Section 3) and in the reduction route, and is not a separate
node.

### 2.3 Infinite centralizers force fixed price one (Theorem C, Corollaries C.1, C.2)

Node: `fpbs-infinite-centralizer-forces-price-one`, with route `-proof`.

**Theorem C.** If `N, M ◁ Gamma` are infinite and commute elementwise, then
`Gamma` has fixed price one. No cost hypothesis is needed.

**Proof.** Put `Z = N ∩ M`.
- If `Z` is infinite, it is an infinite abelian normal subgroup, and the
  classical result applies.
- If `Z` is finite, then `NM/Z ≅ N/Z x M/Z`. Khezeli gives it fixed price one.
- Lemma A lifts this to `NM`, and wq-normality lifts it to `Gamma`.

**Corollary C.1.** If `N ◁ Gamma` is infinite and `C_Gamma(N)` is infinite,
then `Gamma` has fixed price one. In particular this holds whenever the outer
kernel `Q_0 = pi(C_Gamma(N))` is infinite, or `Z(N)` is infinite.

**Corollary C.2.** The same holds if `[N, M]` is finite, or if
`C_{Gamma/F}(NF/F)` is infinite for some finite `F ◁ Gamma`. Pass to
`Gamma/F`, then apply Lemma A.

**Effect on the graph.**
- Case 0 of `fpbs-bounded-cost-normal-via-quotient-trichotomy` extends from
  "infinite amenable subgroup in the outer kernel" to "infinite outer kernel".
- The dead "commuting part of the outer kernel" attempt on the target is
  completed. The earlier attempt stopped at passing from `N x C` down to a
  finite central quotient. The fix is to use the direct product `NC/Z`, which
  needs the good direction of Lemma A.

### 2.4 Reduction of the target to the faithful just-infinite case (Theorem D)

Nodes:
- `fpbs-bounded-cost-just-infinite-faithful-price-one` (claim O, open);
- `fpbs-bounded-cost-fg-torsion-via-just-infinite-reduction` (route to the
  target requiring O and E2).

**Statement O.** Let `N ◁ Gamma` be infinite and satisfy (H). Suppose
`Q = Gamma/N` is infinite, finitely generated, torsion and just-infinite. Also
suppose `C_Gamma(N)` is finite and contained in `N`: the outer action is
faithful and `Z(N)` is finite. Then `Gamma` has fixed price one.

**Theorem D.** O implies T'', which is T' without the outer-kernel hypothesis.
Conversely O is a special case of T'. So O, T' and T'' are equivalent.

**Proof.**
1. By Zorn's lemma, take `P ◁ Q` maximal of infinite index. Then `Q/P` is
   just-infinite, since a union of a chain of infinite-index normal subgroups
   of a finitely generated group has infinite index.
2. Put `N_1 = pi^-1(P)`. It satisfies (H) by Lemma B.
3. If `C_Gamma(N_1)` is infinite, use Corollary C.1.
4. Otherwise `C_Gamma(N_1)` is a finite normal subgroup, and its image in the
   just-infinite group `Q/P` is trivial. So `C_Gamma(N_1) ⊆ N_1`. Apply O.

**A proof of O may also assume:**
- `C_{Gamma/F}(NF/F)` is finite for every finite `F ◁ Gamma` (Corollary C.2);
- `N` does not have fixed price one, since otherwise wq-normality finishes.

**Burnside.** For the split `B(m,n) = N ⋊ B(m-1,n)`, step 3 never applies,
because centralizers are cyclic (`fpbs-burnside-embedding-input`). So O is
needed in full. Nothing here gives fixed price one for free Burnside groups.

## 3. Approaches to O and where each dies

1. **Infinite centralizer or commuting subgroups (Theorem C).**
   - Dies because in O, `C_Gamma(N)` is finite. Every `M ◁ Gamma` commuting
     with `N` lies in it. Corollary C.2 also removes pairs that commute modulo
     a finite normal subgroup.
   - For Burnside groups there is not even a commuting pair of infinite
     subgroups (normal or not), because centralizers are cyclic. So no
     Khezeli-type product sits anywhere inside `Gamma`.
2. **Enlarging the normal subgroup.**
   - Each `N ⊆ Lambda ◁ Gamma` inherits (H) by Lemma B, and fixed price one of
     `Lambda` would lift.
   - Dies because just-infiniteness leaves `Lambda = N`, which is the
     hypothesis, or `Lambda/N` of finite index in `Q`, which is again an
     instance of O.
3. **Intermediate subgroups `Lambda = pi^-1(S)`.**
   - If `S` is an infinite locally finite subgroup of `Q`, then `(Lambda, N)`
     has faithful outer action. It is an instance of the open claim
     `fpbs-bounded-cost-locally-finite-outer-price-one`, and fixed price one
     would lift to `Gamma` because `Lambda ⊇ N` is wq-normal.
   - This reduces O, for quotients containing an infinite locally finite
     subgroup, to that open claim. Examples of such quotients are torsion
     branch groups: Grigorchuk's group contains infinite elementary abelian
     2-subgroups built from involutions with disjoint supports.
   - Dies because that claim is open. Also, for large odd `n` the finite
     subgroups of `B(m-1,n)` are cyclic, so it has no infinite locally finite
     subgroup. This is recalled from Adian and Ol'shanskii and was not fetched.
     Whether its just-infinite quotients have one is unknown.
   - Finite `S` gives nothing new.
4. **Quotient-split actions (Theorem A of `fpbs-quotient-split-actions-have-cost-one`,
   established).**
   - Every free `Gamma`-action with a free factor of `Q` has cost one, and `Q`
     is finitely generated, so all its free actions have finite cost. Hence
     the infimal cost of `Gamma` is one in the T' setting.
   - Dies because fixed price one needs the Bernoulli shift, which has maximal
     cost among free actions by Abert--Weiss maximality (as recorded in
     `fpbs-free-action-cost-at-least-bernoulli-cost`, whose own open statement
     is the converse inequality). In the Bernoulli
     shift `N` acts ergodically, so there is no factor of `Q` and no
     `N`-invariant set of small measure.
   - The weak containment transfer is dead by
     `fpbs-quotient-split-not-bernoulli-contained`.
5. **Cheap graphings of `R_N` on small sets.**
   - Theorem A uses an `N`-invariant set `B` of small measure, on which
     `R_N|B` has unnormalized cost at most `K mu(B)`.
   - If `N` is ergodic, any set `B` of positive measure meets almost every
     `R_N`-class. The induction formula then gives unnormalized cost
     `mu(B) C_{mu_B}(R_N|B) = mu(B) + C(R_N) - 1`, which is not small.
   - So a proof must generate `R_N` more cheaply by using elements outside
     `N`. In Gaboriau's criterion with an infinite-order element in the
     quotient, this comes from Rokhlin towers for that element. A torsion
     quotient has none. This is the known obstruction, and it is the same one
     behind Gaboriau's question on finitely generated normal subgroups with
     torsion quotients. That framing is recalled, not quoted.
6. **Slutsky's criterion (arXiv:2607.20273).**
   - Theorem 1.1 says: if there are finite `F_n ∋ e` with
     `|F_n S F_n^-1| / |F_n|^2 -> 0`, then `Gamma` has fixed price one.
     Corollary 2.5 is the case of finite subgroups `K_n` with
     `min_s |K_n ∩ s K_n s^-1| -> infinity`, and Corollary 1.2 the case of
     infinite amenable q-normal subgroups.
   - In large odd free Burnside groups, amenable subgroups are finite cyclic of
     bounded order. So Corollaries 1.2 and 2.5 do not apply.
   - Theorem 1.1 for these groups was not decided. The product-set growth
     theorem for Burnside groups of Coulon and Steenbock (recalled, not
     fetched) suggests such `F_n` are hard to find there, but its exact form
     was not compared with `F S F^-1`.
7. **L²-Betti numbers.**
   - `beta_1^(2)(Gamma) = 0` in the T' setting. `N` has finite first
     L²-Betti number, since it is at most `C(N) - 1 <= K - 1`, and it is an
     infinite normal subgroup of infinite index. This is Gaboriau's normal
     subgroup theorem for `beta_1^(2)` (Publ. Math. IHÉS 95, 2002), recalled
     with the theorem number unverified.
   - So there is no L² obstruction, but it gives no upper bound on cost. That
     would be the cost versus `beta_1^(2)` problem.
8. **Passing to `Gamma/F` for finite `F`.**
   - One might remove the finite center of `N`. Lemma A goes the right way
     (from `Gamma/F` to `Gamma`), but O's hypothesis (H) would have to pass to
     `N/(N ∩ F)`.
   - Dies because that needs the unproved converse direction of Lemma A. It
     is not needed, since O allows finite `Z(N)`.

## 4. Sanity checks on the hypotheses

- **(H) is essential.**
  - Take `F_2 -> B(2,n)` with kernel `N`. `N` is free of infinite rank, so its
    free actions have infinite cost and (H) fails.
  - Meanwhile `F_2` has fixed price 2. So the conclusion fails without (H).
- **Infinite `Q` is essential.** `Gamma = N = F_2` satisfies (H) with `K = 2`
  and has price 2.
- **The outer-kernel hypothesis of T' is redundant**, by Theorem D.

## 5. Literature (gate of 2026-09-16)

- **arXiv:2509.08325 (Khezeli).** Products of two infinite countable groups
  have fixed price one. HTML read 2026-09-16. It is used as [KHE] and its
  proof was not rechecked.
  - Its introduction lists "groups with an infinite normal subgroup" among
    fixed-price-one classes. Read literally this is false (free groups), so it
    is not relied upon.
- **arXiv:2607.20273v1 (Slutsky), "A Product-Neighbourhood Criterion for Fixed
  Price One".** HTML read 2026-09-16. The statements of Theorem 1.1,
  Corollary 1.2 and Corollary 2.5 were extracted and paraphrased above.
- **arXiv:2608.20472 (Donoso, Echenique, Silva).** Infimal cost one for large
  odd free Burnside groups. Taken from the repo nodes that cite it, and not
  refetched this session.
- **arXiv:2510.05459 (Bevilacqua and Bowen).** Taken from the repo nodes, and
  not refetched.
- **D. Gaboriau, "Coût des relations d'équivalence et des groupes", Invent.
  Math. 139 (2000).** PDF fetched 2026-09-16, and the text was extracted with a
  zlib decode that lost the math symbols. Critère VI.24 (2) (normal criterion)
  and the surrounding Proposition VI.23 were located. The inequality is not
  quoted, because the symbols were lost, and Lemma B was proved independently.
- **Gaboriau lecture notes, Exercise 1.17 (small complete sections).** Used
  through `fpbs-wq-normal-price-one-subgroup-forces-price-one-proof`, and not
  refetched. Lemma B.0 gives a self-contained proof.
- **Recalled only, unverified:**
  - Gaboriau, Publ. Math. IHÉS 95 (2002), the `beta_1^(2)` normal subgroup
    theorem;
  - Adian and Ol'shanskii, finite subgroups of large odd free Burnside groups
    are cyclic;
  - Coulon and Steenbock, product set growth in Burnside groups.
- **arXiv API search for 2024–2026 papers on "fixed price" with "normal
  subgroup" or "torsion quotient".** Attempted on 2026-09-16. The export API
  gave a connection reset and then "Rate exceeded", and the listing HTML
  reset. A retry at about 03:40 UTC failed the same way. A fetch of the
  math.GR past-week listing returned HTTP 429, and the session's web-search
  budget was exhausted. So no fresh listing beyond the papers above was
  obtained. No paper found or
  read settles T' or O.

## 6. Assessment

**Outcome: reduction.** The target stays open.

**Proved.**
- Lemma A and Theorem C with Corollaries C.1 and C.2 are unconditional, given
  the imports. They settle every infinite outer kernel and every infinite
  centralizer with no cost hypothesis.
- Theorem D shows that the target is equivalent to the faithful just-infinite
  case O. A proof of O would also give the target without its outer-kernel
  hypothesis.

**Weakest steps.**
1. Theorem C depends on Khezeli's theorem, which was not rechecked.
2. Lemma A's measure-theoretic details: the Borel fundamental domain, the
   piecewise measure preservation, and the normalization in the induction
   formula. These were checked by hand, and the formula was checked in the
   finite-group sanity case `Gamma = F`. There the quotient relation on `D` is
   trivial, with cost 0, and the formula returns price `1 - 1/|F|`.

**Confidence.** High in the reduction, medium-high in Lemma A's written
details. No confidence either way about O. It contains fixed price one for
large odd free Burnside groups, and the one mechanism known to push cost below
the normal subgroup's bound (Rokhlin towers in the quotient) is unavailable.

**Validation.** check.sh was run on all seven research paths, including the
artifact. The final exit code is recorded in the swarm return.

## Referee (2026-09-16)

**Checked.**
- Lemma A (finite normal kernel lift): the Borel fundamental domain, the
  well-definedness of `q . x = r(gamma x)` via normality, the injectivity and
  piecewise measure preservation, freeness, the identification of the orbit
  relation with `R_Gamma|D`, and the normalization `mu(D) = 1/|F|` against
  [IND] `C(R) - 1 = mu(Y)(C_(mu_Y)(R|Y) - 1)`. No gap found.
- Lemma B.0 (small complete sections): the separating-family colouring gives
  `c(x) != c(s x)` coordinatewise at `s`; the greedy construction is Borel,
  independent (using that `S` is symmetric) and maximal, so `X = A ∪ S A`.
  Lemma B: the connection `x ~_N w x -> gamma_j w x ~_N lambda x` is correct.
- Theorem C and Corollaries C.1, C.2: the case split on `Z = N ∩ M`, the
  internal direct product `L/Z`, Fact 1.1 (`Q_0 = pi(C_Gamma(N))`), and the
  normality of `[N, M]`. The wq-normal definition used matches the repo's
  `fpbs-wq-normal-hull-is-almost-malnormal` convention through fact (i) of
  `fpbs-amenable-outer-kernel-forces-price-one-proof`.
- Theorem D: the Zorn argument (a finite-index union is finitely generated,
  hence equals a chain member), Lemma D.2, and the containment
  `C_Gamma(N_1) ⊆ N_1`. The outer-kernel hypothesis of the target is indeed
  unused. The converse (O is a special case of the target) is correct.
- Literature, fetched 2026-09-16: arXiv:2509.08325 (Khezeli, v4 revised
  2026-01-04), Theorem 1.1 "The product of any two infinite countable groups
  has fixed price one"; no corollary on commuting normal subgroups or
  infinite centralizers is stated there. The introduction sentence on
  "groups with an infinite normal subgroup" is quoted correctly by the solver.
  arXiv:2607.20273v1 (Slutsky, 2026-07-22): Theorem 1.1, Corollary 1.2 and
  Corollary 2.5 match the paraphrases in Section 3.6. A web search for later
  statements of Theorem C could not be run (session search budget exhausted),
  so novelty of Theorem C is unaudited beyond these two papers; the artifact
  already claims no novelty beyond the written proof.
- Duplicates: `bin/cairn search --similar` on the three new claims finds no
  duplicate. Id lengths and '## Attempts' on the new hole are in order.

**Changed.**
- Section 3.4 of these notes cited `fpbs-free-action-cost-at-least-bernoulli-cost`
  for maximality of Bernoulli cost. That open claim is the converse
  inequality; maximality is Abert--Weiss, as recorded there. Fixed.
- `fpbs-bounded-cost-just-infinite-faithful-price-one`: the Burnside paragraph
  now says `m >= 3` and why the enlarged pair is an instance.

**Not changed.** The committed target
`fpbs-bounded-cost-fg-torsion-quotient-price-one` still lists the "Commuting
part of the outer kernel" attempt as dead; it is superseded by
`fpbs-infinite-centralizer-forces-price-one`, and its outer-kernel hypothesis
is shown redundant by the new route. The target node was not edited.

**Verdict.** Sound. Lemma A, Lemma B and Theorem C are complete given the
imported inputs ([IND], Khezeli, [WQ]); Theorem D is a correct reduction of
the target to the open claim O. Landed with the two small fixes above.
