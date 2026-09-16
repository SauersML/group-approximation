# stw99-problem-lxiv-cu-of-villadsen-toms: swarm attack, 2026-09-16

- **Target and hole worked.** The root `stw99-problem-lxiv-cu-of-villadsen-toms`,
  STW Problem LXIV. It is the same question as Gardella--Perera Problems 16.1--16.3.
- **Outcome.** Partial progress. There is no computation of Cu(A) for a Villadsen or
  Toms algebra. No second unit-preserving morphism was constructed, and none was
  excluded.
- **Result.** Two established lemma pairs pin down where a second morphism can differ
  from a given one, and which detectors cannot see the difference.
- **Full proofs.** `research/artifacts/stw64-z-scales-rc-offset-2026-09-16.md`.

## 1. Setup

- **Cu(Z).** Robert (arXiv:1007.1964v3, Section 6.3) gives
  Cu(Z) = N disjointUnion (0,infinity]. The compact classes are n and the soft
  classes are t'. The relations are:
  - n+t'=(n+t)';
  - n<=t' iff n<t, and t'<=n iff t<=n;
  - t'<<r' iff t<r;
  - t'=sup_{r<t} r'.
- **Unit-preserving morphisms.** A unit-preserving Cu-morphism f:Cu(Z)->Cu(A)
  sends n to n[1_A]. It is determined by its soft scale t -> f(t').
- **Radius of comparison.** rc(A) is Toms's radius in the Cu form of APRT
  (arXiv:1809.03984v3, 8.6). It is the infimum of r in (0,infinity] such that
  lambda(x)+r<=lambda(y) on F_u implies x<=y.
- **Supersoft scale.** Under the stable-rank-one hypotheses of
  `stw64-supersoft-calculus`, s_c=alpha(c*[1]-hat).
- **Already established before today.**
  - `stw64-supersoft-gap-is-comparison-radius`: s_a<<s_b implies rc<=b-a, and b-a>rc
    implies s_a<<s_b.
  - `stw64-z-maps-avoid-supersoft-classes`: if rc>0, then f(t')!=s_t.
  - `stw99-lxiv-pair-lifts-to-lxiii-refuter`: a distinct pair lifts to a LXIII refuter
    by Robert's classification.

## 2. Status gate (checked 2026-09-16)

- **STW, arXiv:2506.10902v2.** Problem LXIV was quoted from converted HTML. It is
  still stated as open. The same section says Toms's Villadsen-type counterexamples
  contain unital copies of Z.
- **Gardella--Perera, arXiv:2212.02290v2.** Problems 16.1--16.3 were quoted. 16.3 asks
  for "two distinct Cu-morphisms Cu(Z)->Cu(A) preserving unit classes".
- **Elliott--Niu, *Remarks on Villadsen algebras, II*, arXiv:2510.13695v2.**
  - They classify UHF-/AF-Villadsen algebras through the comparison-radius function.
  - They do not compute Cu.
  - Quote: "The question of what the structure of the Cuntz semigroup for Villadsen
    algebras actually is is clearly of considerable interest."
- **APRT, arXiv:1809.03984v3.** Checked:
  - Section 2: weak cancellation, and cancellation of compact elements for stable rank
    one;
  - Definition 8.1, Proposition 8.2, Theorem 8.4 and paragraph 8.6: the rc definition,
    quoted in the artifact.
- **Robert, *Strict comparison and selflessness*, arXiv:2609.15776v1 (2026-09-14).**
  The abstract is about monotracial strict comparison, which is the rc=0 regime. It is
  not relevant to positive-radius targets.
- **Ciuperca--Elliott, arXiv:0707.2220v2, and Robert--Santiago, arXiv:0905.0680v1.**
  Existence and abstracts were verified through the arXiv API. They concern
  classification of homomorphisms from C_0(0,1] by Cu. I could not extract the PDF
  text, so whether they contain a shift-type distance between Cu-morphisms is
  **UNVERIFIED**. The session's web-search budget (200/200) was exhausted before this
  prior-art check.
- **Novelty.** None is claimed for the shift metric.

Conclusion: LXIV remains open as of 2026-09-16 in every source checked. This is a
targeted check, not a certification.

## 3. What was proven (landed as nodes; check.sh exit 0, both claims ESTABLISHED)

### 3a. `stw64-unital-z-maps-rc-shift-close`

Route: `stw64-unital-z-maps-shift-proof`, `requires: []`. The hypothesis is any
unital A.

1. If b-a>=rc(A), then h(a')<=f(b') for all unit-preserving f,h. The strict case uses
   equal ranks lambda(f(t'))=t*lambda(u) together with an admissible constant
   R=b-a. The boundary case takes a supremum.
2. If rc(A)=0, then f=h. This is the Cu-level core of
   `stw63-strict-comparison-cu-collapse-proof`, with no stable rank one hypothesis.
3. The shift distance delta(f,h) is attained and is an extended metric with
   delta<=rc(A). So the space of unit-preserving morphisms has diameter at most rc(A).
4. Disagreement is a germ at 0. Under weak cancellation it is also invariant under
   integer translation.

**Combination with a sibling agent's result.** A sibling agent's not-yet-landed node
`stw63-distinct-z-cu-maps-need-perforation-witness` says f!=h iff there is a rational
pair 0<t<s<=1 with f(t') not below h(s') (or swapped). Item 1 sharpens the gap
condition on such a pair to s-t<rc(A), strictly. That note's unlanded "gap bound"
said s-t<=min(1,rc(B)). When both nodes land, a `distinct_from` should record that
theirs is order-theoretic in arbitrary S with no rc, while this one is the
quantitative rc bound.

### 3b. `stw64-z-scales-rc-below-supersoft`

Route: `stw64-z-scales-rc-offset-proof`, which requires `stw64-supersoft-calculus` and
`stw64-supersoft-gap-is-comparison-radius`. For any unit-preserving f:

- (a) f(b')<=s_a iff b<=a.
- (b) s_a<=f(b') iff b-a>=rc. The boundary case is decided.
- (c) s_a<<f(b') iff b-a>rc.
- (d) f(b')<<s_a iff b<a.
- (e) s_d<=sum_i f_i(a_i') iff sum a_i - d >=rc, for any finite family of possibly
  distinct unit-preserving morphisms f_i.

**Invisibility corollary.** On the labels {0, n, t', [s_c], infinity}, the addition
table, <= and << are independent of f. In particular:

- nu<=s_c iff n<c;
- s_c<=nu iff n-c>=rc;
- f(t')+s_c=s_{t+c}.

The key step in the converse of (e) is this. From s_d<=x<<x_eta<=s_{r+k*eta}, the
gap formula gives rc<=r+k*eta-d. Fact 2.0 (nonzero finite-rank soft classes are not
compact) excludes d=r+k*eta.

### 3c. Consequences for a hypothetical pair f!=h (simple unital sr1 target)

- 0<delta(f,h)<=rc(A). The pair must disagree at arbitrarily small levels and, by
  weak cancellation, at every integer translate.
- Comparisons of values of one morphism with integers or with canonical supersoft
  classes cannot detect the difference. Neither can comparisons of some s_d with a
  finite sum of values of possibly different morphisms (item (e)). Mixed comparisons
  between values of two different morphisms are not covered.
- Detection needs one of the following:
  - a mixed comparison h(a')<=f(b') inside the window 0<=b-a<rc(A);
  - a comparison against a class outside the canonical scalar scales: projections,
    classes of nonconstant rank, or soft classes not of the form alpha(c*u-hat).

## 4. Approaches tried and exactly where each dies

1. **Meet f∧h in the inf-semilattice Cu(A).** APRT Theorem 3.8, checked in the
   converted text, says that separable stable rank one gives an inf-semilattice
   ordered semigroup, with (x+z)∧(y+z)=(x∧y)+z (their (3.1)). By (3.1),
   k(t)=f(t')∧h(t') satisfies
   k(t)+k(r) = k(t+r) ∧ (f(t')+h(r')) ∧ (h(t')+f(r')).
   So k is additive iff k(t+r)<=f(t')+h(r') and k(t+r)<=h(t')+f(r'). These are
   comparisons between classes of equal rank, so the rc criterion, which needs a
   positive rank gap, cannot supply them when rc>0. Dies at additivity.
2. **Averaging m(t')=f((t/2)')+h((t/2)').** It is additive in t and preserves suprema
   and <<. For a unit-preserving morphism one needs m(1')<=u and m((1+t)')=u+m(t'),
   i.e. f((1/2)')+h((1/2)') must behave like the unit. Rank equality shows only that
   m(1') has the rank of u. The rc criterion needs a positive rank gap, so it gives
   nothing here. Dies at the unit relations, which are again equal-rank or window
   comparisons.
3. **Tensoring with Z.** Z-stable uniqueness collapses both maps after the first-factor
   map A->A⊗Z. Reflecting soft comparisons back
   (`stw99-lxxvi-first-factor-reflects-soft-comparisons`) assumes almost unperforated
   Cu(A), which fails when rc>0. Dies at reflection.
4. **Canonical supersoft scale as the second morphism.** It is excluded, and 3b
   sharpens this: every unit-preserving scale sits below the supersoft scale with
   offset exactly rc at every level.
5. **Twisted embeddings into Villadsen type I building blocks.** A Villadsen type I
   algebra contains the UHF algebra of constant matrices unitally, which gives a
   canonical f_0 through Z->UHF.
   - A second map would need Z_{p,q} images whose eigenvalue maps are nonconstant, with
     range projections forming nontrivial bundles over the high-dimensional base
     spaces.
   - The Villadsen Chern-class obstruction must survive dilution by point evaluations.
   - Given 3a, it must also show up at small levels t, below rc.
   - I did not carry out a computation. The sibling note (Section 4 item 6 of
     `notes/stw63-distinct-cu-maps-counterexample-swarm-2026-09-16.md`) gives a
     heuristic reason why Euler-class twisting alone may not separate additive scales.
6. **Toy abstract Cu-semigroups with rc>0 and two unit scales.** Label-gap models
   violated (O2)/(O3)-compatibility unless further element types were added. The
   sibling agent reports the same failure. Abandoned. No script was kept, so there is
   no `experiments/` directory for this attack.

## 5. What remains open

- LXIV itself: compute Cu of Toms's sr1 Villadsen-type algebras, and decide whether a
  second unit-preserving Cu(Z)->Cu(A) exists.
- The only room left for a second morphism:
  - soft images at small levels, within shift distance at most rc(A) of the given one;
  - separated only by comparisons inside the window or against non-scalar classes.
- A concrete next test: in a Villadsen type I building block C(X)⊗M_n with
  dim X/n large, look for a Z_{p,q}-type map whose soft images at levels t<rc have the
  right ranks but carry nontrivial range bundles. Then check the mixed comparison
  f_0(a')<=f_1(b') for a<b<a+rc. Elliott--Li--Niu (arXiv:2209.10649v4, Theorem 3.4:
  rc=mdim/2, as reported in the sibling note; not re-checked by me) gives the window
  size.
- Any such pair would refute LXIII by `stw99-lxiv-pair-lifts-to-lxiii-refuter`.

## 6. Files written

- `research/artifacts/stw64-z-scales-rc-offset-2026-09-16.md`
- `research/stw64-unital-z-maps-rc-shift-close.md` (claim)
- `research/stw64-unital-z-maps-shift-proof.md` (route, `requires: []`)
- `research/stw64-z-scales-rc-below-supersoft.md` (claim)
- `research/stw64-z-scales-rc-offset-proof.md` (route)
- this note

## Referee (2026-09-16)

**Checked.**

- Read all six files, plus the imported nodes:
  - `stw64-supersoft-calculus` and its citation route;
  - `stw64-supersoft-gap-is-comparison-radius` and its proof route;
  - `stw64-z-maps-avoid-supersoft-classes`;
  - `stw63-strict-comparison-cu-collapse-proof`;
  - the 2026-09-04 artifact.
- Re-derived every step of Theorem 1, Proposition 1.2, Corollary 1.3, Theorem 2(a)-(e)
  and Corollary 2.1 by hand:
  - Fact 0.1 uses m-1<nt<=m, and holds for every functional, including lambda(u)=0 or
    infinity.
  - The converse of (e) is sound. The solver's "weakest step" is fine: s_d<=x gives
    d<=r<r+k*eta, so the gap implication (G) applies. Fact 2.0 is not even needed
    there.
  - Relations with the top: x<<sup_n nu iff x<=mu for some m.
- Fetched the APRT arXiv:1809.03984v3 HTML and grepped it:
  - Paragraph 8.6 defines rc exactly as used: non-strict lambda(x)+r<=lambda(y) over
    F_u(Cu(A)), with r in (0,infinity] and x,y in Cu(A).
  - Paragraph 2.5 and its lemma give weak cancellation in the (x+z<=y+z', z'<<z) form,
    and the remark after it gives cancellation of compact elements.
  - Theorem 3.8 and (3.1) give inf-semilattice ordering for separable stable rank
    one.
- Verified the STW LXIV quote (arXiv:2506.10902v2 HTML) and the Elliott--Niu quote
  (arXiv:2510.13695v2 HTML).
- Confirmed via the arXiv API that these exist with the stated titles and authors:
  - Robert, arXiv:2609.15776 (2026-09-14);
  - Ciuperca--Elliott, arXiv:0707.2220;
  - Robert--Santiago, arXiv:0905.0680;
  - Elliott--Li--Niu, arXiv:2209.10649.
- The shift-metric prior-art check remains unverified, as the solver said. No novelty
  is claimed.
- `bin/cairn search --similar` on both claims: no duplicate. The nearest nodes are
  already covered by distinct_from.

**Changed.**

- Claim `stw64-unital-z-maps-rc-shift-close`, item 4. The statement said "iff ... for
  every n", which is trivially true by taking n=0. It now says "for each n", which is
  what the proof shows. The route and artifact were adjusted, with the APRT 2.5 source
  named.
- Claim `stw64-z-scales-rc-below-supersoft`. The invisibility sentence, "cannot be
  detected ... by sums of these with values of unit-preserving morphisms", was
  overbroad: nu+h(a')<=f(b') is a sum-versus-value comparison that is not covered. It
  now names exactly what is covered, and says that mixed comparisons between two
  morphisms are not. The same fix was made in artifact Section 3 and in note 3c.
- Route `stw64-z-scales-rc-offset-proof`: noted that d<r+k*eta follows from ranks and
  eta>0.
- Artifact:
  - Section 3 item 1 wrongly attributed "rc(A)>0" to the 2026-09-04 obstruction. It
    now cites Corollary 1.1.
  - Section 3 item 5, on agreement after tensoring with Z, is marked as a remark that
    is not proved here.
  - The status gate referred to "Section 2" for the shift metric. It is Section 1.
- The sibling note cited in approach 5
  (`notes/stw63-distinct-cu-maps-counterexample-swarm-2026-09-16.md`) belongs to
  another agent and is not landed by this commit.

**Verdict.** Sound. Both claims are correct, elementary consequences of the Cu(Z)
relations, the APRT 8.6 definition and the already established supersoft calculus and
gap nodes. The `requires: []` route imports only Robert's Cu(Z) computation and
verified APRT definitions and remarks. Landed with wording fixes. LXIV and LXIII remain
open.
