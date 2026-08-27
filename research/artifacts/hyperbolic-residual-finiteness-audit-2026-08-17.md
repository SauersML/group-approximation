# 2026-08-17 — Residual finiteness of hyperbolic groups: ingestion audit of an external attempt

Source: a user-supplied external resolution attempt, *"Residual finiteness of
hyperbolic groups: attempted resolution"*, dated 17 August 2026, unrefereed,
written against a snapshot of this repository.  This file records the
ingestion audit and carries the proofs the new graph nodes cite; the canonical
statements live in the graph.

**Headline of the source, which this audit confirms.**  The question *is every
word-hyperbolic group residually finite?* is **not** resolved by the supplied
material, and the source says so itself in its own words ("I did **not**
obtain a valid proof or a valid counterexample").  What it produces is a
reduction-and-obstruction package: two attack families are killed outright,
four reductions are exact, and one route is diagnosed precisely at the point
where it stops.

Nothing below is claimed as a resolution of the open problem, and nothing in
the graph region built from this file establishes
`non-residually-finite-hyperbolic-group`.

---

## A. Citation verification status

Read from source **this session** (2026-08-17) via the arXiv abstract pages
and, where noted, the full HTML.  Quotations are verbatim.

| Source | Status | What was checked |
|---|---|---|
| Oyakawa, arXiv:2409.09527 | **verified** (v1 2024-09-14, v2 2024-12-02, **v3 2026-03-13**) | title *Infinite graph product of groups I: Geometry of the extension graph*; Theorem 1.3 and Corollary 1.4 read from the v3 HTML, quoted below |
| Needham, arXiv:2509.11170 | **verified** (2025-09-14) | title *Residual Finiteness of Graph Wreath Products*, author Amy Needham; abstract "We prove necessary and sufficient conditions for when graph wreath products are residually finite, generalising known results for the permutational wreath product and free product cases."; Theorem 1.1 read from the HTML, quoted below |
| Belegradek–Osin, arXiv:math/0605553 | **verified** | abstract quoted below; the Rips-construction statement the source uses is the abstract's own sentence |
| Osin, arXiv:math/0510195 | **partially verified** | title *Peripheral fillings of relatively hyperbolic groups* and abstract confirmed; the abstract does **not** contain the finite-set/injectivity clause, so the precise form used here is the published Theorem 1.1 (IMRN 2007) as it is universally quoted, **not** re-read from the paper body today.  This is the one literature input of the region that carries an unclosed trust surface |
| Cui–Wan, arXiv:2604.04007 (2026-04-05) | **verified** | full text searched; it contains "It is an open conjecture that every hyperbolic group is residually finite."  This is the region's evidence that the problem is open as of 2026-04 |
| Chapman–Peled, arXiv:2509.21566 | already in the graph | `random-complex-linear-cocycle-stability`, `cocycle-stability-nonsofic-route` |
| Kun–Thom, arXiv:2608.06222 | already verified in this repo | `research/artifacts/kun-thom-2608-06222-verified.md`, Theorem B quoted below |
| Fournier-Facio, arXiv:2608.02025 | **verified** | *A torsion-free non-sofic group* (2026-08-03, rev. 2026-08-14) |

### One citation correction

The source's reference list contains

> F. Fournier-Facio, 2025 work on nonapproximable relatively hyperbolic
> groups, arXiv:2512.09180.

arXiv:2512.09180 is real but is **not** that paper.  It is Fournier-Facio,
*Stability, approximable quotients, and higher property (T)* (2025-12-09, rev.
2026-06-08), abstract: "We construct a wealth of groups that are finitely
presented, Frobenius stable, have property (T), but are very far from having
property (T₂).  Our method also shows that property (T₂) does not pass to
quotients."  The description "nonapproximable relatively hyperbolic groups" is
a mislabel.  No claim in the graph region rests on that reference; §3 of the
source rests only on the filling theorem.

### Verbatim quotations relied on

Oyakawa, arXiv:2409.09527v3, Corollary 1.4:

> Suppose that Γ is a locally finite hyperbolic graph with girth(Γ)>20 and
> that a group G acts on Γ properly and cocompactly.  Let H be a finite group
> and define 𝒢={G_v}_{v∈V(Γ)} by G_v=H for any v∈V(Γ).  Then, Γ𝒢⋊G is
> hyperbolic.

Oyakawa, Theorem 1.3:

> Suppose that Γ is a fine hyperbolic graph with girth(Γ)>20 and that a
> finitely generated group G acts on Γ satisfying the following two
> conditions.  (1) E(Γ)/G is finite and for any e∈E(Γ), Stab_G(e) is finite.
> (2) For any v∈V(Γ), Stab_G(v) is finitely generated.  Let H be a finite
> group and define 𝒢={G_v}_{v∈V(Γ)} by G_v=H for any v∈V(Γ).  Then, there
> exists a finite set F⊂V(Γ) such that Γ𝒢⋊G is hyperbolic relative to the
> collection {⟨Stab_G(v), G_w ∣ w∈St_Γ(v)⟩}_{v∈F}.

Oyakawa also records, in the same paper, that investigating residual
finiteness of these hyperbolic groups "might shed light on the long-standing
open problem asking whether every hyperbolic group is residually finite".
That sentence is what §5 below answers, negatively, for the proper-cocompact
case.

Needham, arXiv:2509.11170, Theorem 1.1 (conditions, as read from the HTML):
for groups `Γ, Δ` and a graph `G=(V,E)` on which `Γ` acts, the graph wreath
product `G(Δ)⋊Γ` is residually finite if and only if

1. `Γ, Δ` are residually finite;
2. either `Δ` is abelian and for all neighbouring `v,w∈V` there is a finite
   index subgroup `K≤Γ` such that `w∉Kv`, or for all `v` there is some finite
   index subgroup `K≤Γ` such that `Kv∩N(v)=∅`;
3. for all `v,w` not neighbouring and not equal there is a finite index
   `K≤Γ` such that `Kw∩(N(v)∪{v})=∅`.

Belegradek–Osin, arXiv:math/0605553, abstract:

> We show that for any non-elementary hyperbolic group H and any finitely
> presented group Q, there exists a short exact sequence 1→N→G→Q→1, where G
> is a hyperbolic group and N is a quotient group of H.

Kun–Thom, arXiv:2608.06222, Theorem B (verbatim, from the repo's verified
artifact):

> Let G be a sofic group with Kazhdan's property (T), and let Γ≤G be an
> infranormal subgroup with Kazhdan's property (T).  Then C_G(Γ) is normal
> in G.

---

## B. What the graph took, with the audit's corrections

### B.1 Centralizer rigidity (source §2) — accepted, and **reduced to an existing node**

Source Theorem 2.1: if `G` is hyperbolic, `Γ≤G` is non-elementary and
`tΓt^(-1)≤Γ`, then `C_G(Γ)=tC_G(Γ)t^(-1)`.

The proof is correct.  It has exactly two inputs, and the audit separates
them because the second one is **already in this graph**:

1. `C_G(Γ)` is *finite*.  A non-elementary subgroup contains independent
   infinite-order loxodromics `x,y`; centralizers of infinite-order elements
   in a hyperbolic group are virtually cyclic; and
   `C_G(Γ) ≤ C_G(x)∩C_G(y)`, which is finite, since an infinite subgroup of
   the virtually cyclic `C_G(x)` contains an infinite-order element and would
   force `x,y` into a common elementary subgroup.
2. A finite subgroup that is compressed is normalized.  `tΓt^(-1)≤Γ` gives
   `C_G(Γ) ≤ C_G(tΓt^(-1)) = tC_G(Γ)t^(-1)`, i.e. `t^(-1)` lies in the
   compression semigroup of `C_G(Γ)`; for a finite subgroup the compression
   semigroup **is** the normalizer.

Step 2 is `finite-infranormal-subgroup-is-normal`, established here since
2026-08-14.  So the new content of source §2 is step 1 plus the consequence,
and the graph records it that way (`hyperbolic-nonelementary-centralizer-finite`
→ `hyperbolic-compression-centralizer-rigidity`) rather than as a fresh
theorem.

Corollary (source 2.2), accepted: with `c∈C_G(Γ)`, `d=tct^(-1)` and `a∈Γ`,
`[d,a]=1` **in `G`**, so the distinguished commutator of the
finite-residual compression witness is trivial in the ambient group, not
merely in its finite quotients.  There is nothing left for a finite quotient
to kill.

Corollary (source 2.4), accepted: the free-lamp repair fails for the same
reason.  With lamp generators indexed by cosets and distinct coordinates in
distinct free factors, `d=c_(tΓ)` and `γdγ^(-1)=c_(γtΓ)` are distinct
generators of distinct free factors for `γ∈Γ∖tΓt^(-1)`, so `[d,γ]≠1`, which
Theorem 2.1 forbids.

**Audit strengthening of source Corollary 2.3.**  The source states that in a
hyperbolic ambient group the Kun–Thom Theorem B conclusion is automatic *for
non-elementary* `Γ`.  It is automatic with no elementarity hypothesis at all,
by a two-case argument:

- `Γ` infinite with property (T): infinite elementary subgroups of hyperbolic
  groups are virtually cyclic, hence infinite amenable, hence do not have (T);
  so `Γ` is non-elementary, `C_G(Γ)` is finite, and every `g∈P_Γ` normalizes
  it (as in step 2 above, applied to `g^(-1)`), so infranormality gives
  `C_G(Γ)⊴G`.
- `Γ` finite: then `Γ` itself is finite and infranormal, hence normal by
  `finite-infranormal-subgroup-is-normal`, and the centralizer of a normal
  subgroup is normal.

So for **every** infranormal property-(T) subgroup of a word-hyperbolic group,
`C_G(Γ)⊴G` unconditionally, and the contrapositive of Kun–Thom Theorem B can
never witness non-soficity of a hyperbolic group.

### B.2 Relative filling reduction (source §3) — accepted, with the trust surface named

Source Theorem 3.1: if `G` is hyperbolic relative to finitely many finitely
generated **residually finite** peripherals and `G` is not residually finite,
then some ordinary word-hyperbolic quotient of `G` is not residually finite.

Proof as given: pick `1≠w` in the finite residual of `G`; the filling theorem
supplies, for the finite set `{w}`, a finite set `B_i⊂P_i∖{1}` such that any
`N_i⊴P_i` with `N_i∩B_i=∅` yields a quotient that is relatively hyperbolic
with respect to `{P_i/N_i}` and injective on `{w}`; residual finiteness of
`P_i` supplies such `N_i` of **finite index** (intersect one witness per
element of `B_i`); a group hyperbolic relative to finite subgroups is
word-hyperbolic; and every finite quotient of the filling pulls back to a
finite quotient of `G`, which kills `w`, so `π(w)≠1` lies in the finite
residual of the filling.

Accepted.  The only external input is the filling theorem, whose precise
statement was **not** re-read from the paper body today (see §A); the graph
carries it as its own citation node so that the trust surface is visible
rather than absorbed.

Consequence recorded in the graph: producing a non-residually-finite
relatively hyperbolic group with residually finite peripherals is *already* a
solution of the open problem, which is why no such construction can be
expected to be easy.

### B.3 Finite central extensions (source §4) — accepted, and flagged as classical

Source Theorem 4.1: for `H` residually finite, `A` finite abelian with trivial
action and `α∈H^2(H;A)`, the central extension `E_α` is residually finite iff
`res^H_(H_0)(α)=0` for some finite-index `H_0≤H` iff the extension virtually
splits.

Both directions are correct as written:

- RF ⟹ virtual splitting: `A` is finite, so intersecting one finite-index
  normal subgroup per nontrivial element of `A` gives `L⊴_f E_α` with
  `L∩A=1`; then `p|_L` is an isomorphism onto `H_0=p(L)≤_f H` and its inverse
  is a section over `H_0`.
- virtual splitting ⟹ RF: `K=s(H_0)` has finite index and meets `A`
  trivially, its normal core still does (as `A` is central), so `A` embeds in
  a finite quotient of `E_α`; elements outside `A` are separated through
  `p` and residual finiteness of `H`.

The audit's one correction is one of attribution, not of content: this
equivalence is **classical folklore**, the standard mechanism behind Deligne's
non-residually-finite central extension of `Sp_4(ℤ)` and behind Hill's
arithmetic constructions.  The source presents it as a deduction of the
attempt; the graph records it as an established classical criterion, because
what the region actually needs from it is the reduction it powers.

Accepted consequence (source Corollary 4.2): the counterexample target is a
residually finite hyperbolic `H`, a prime `p`, and `0≠α∈H^2(H;C_p)` whose
restriction to *every* finite-index subgroup is nonzero; `E_α` is then
hyperbolic (finite extensions preserve hyperbolicity) and not residually
finite.

The source's profinite remark is also accepted in the direction it is used:
if `α` is in the image of `H^2_cont(Ĥ;A)→H^2(H;A)` then `E_α` is residually
finite, because the pullback of the profinite extension embeds in
`Ẽ×H`, a product of two residually finite groups.  So a persistent class must
lie outside that image.

### B.4 Oyakawa + Needham (source §5) — accepted, and this is the region's second kill

Source Theorem 5.1: under Oyakawa's Corollary 1.4 hypotheses with `H≠1`
finite, the graph-wreath product `X(H)⋊G` is residually finite **iff** `G` is.

Checked against the verbatim conditions of Needham Theorem 1.1 quoted in §A:

- necessity: `G` embeds in the semidirect product and residual finiteness
  passes to subgroups;
- Needham condition 1: `H` is finite hence residually finite, `G` is
  residually finite by hypothesis;
- Needham condition 2, second alternative: fix `v`; properness makes
  `Stab_G(v)` finite and local finiteness makes `N(v)` finite, so
  `F_v={g:gv∈N(v)}` is a finite union of cosets of a finite stabilizer, hence
  finite, and `1∉F_v` because the graph is simplicial; residual finiteness
  gives `K⊴_f G` avoiding `F_v`, i.e. `Kv∩N(v)=∅`;
- Needham condition 3: for `v≠w` non-adjacent, `F_(v,w)={g:gw∈N(v)∪{v}}` is
  finite for the same reason and `1∉F_(v,w)`, so a finite-index `K` avoiding
  it gives `Kw∩(N(v)∪{v})=∅`.

Note the alternative used in condition 2 is the one that does **not** require
`Δ` abelian, so the criterion is met whether or not `H` is abelian.

Consequence, and it is sharp: Oyakawa's own suggestion that these hyperbolic
graph-wreath products might bear on the open problem is answered negatively
in the proper-cocompact case.  If `X(H)⋊G` fails residual finiteness then `G`
fails it, and `G` — acting properly cocompactly on a locally finite hyperbolic
graph — is itself a hyperbolic group by Milnor–Švarc.  The construction can
therefore never produce the *first* counterexample.

The relative case (Oyakawa Theorem 1.3) is **not** closed by this argument and
the source does not close it either; the graph keeps it as prose inside the
dead route rather than as a claim, because making Needham's conditions fail
while keeping every Oyakawa peripheral residually finite is itself a strong
relative-separability statement of the same difficulty.

### B.5 Rips reduction (source §6) — accepted as a route, not as progress

Source Proposition 6.1: if `1→N→G→Q→1` with `Q` not residually finite and `N`
having no nontrivial finite quotient, then `G` is not residually finite.
Trivially correct: every finite quotient of `G` kills `N`, hence factors
through `Q`, hence kills any lift of an element of the finite residual of `Q`.

The audit agrees with the source's own warning about circularity, and states
it more precisely.  Belegradek–Osin give `N` as a quotient of a chosen
non-elementary hyperbolic `H`; they do **not** control the finite residual of
`N`.  Their own applications note that a hyperbolic group with no nontrivial
finite quotients would suffice for a related purpose, and that the existence
of such a group is equivalent to the existence of a non-residually-finite
hyperbolic group.  The route is therefore recorded with its missing input
stated as a claim in its own right — "make the Rips kernel have no finite
quotients without assuming the answer" — and that claim is open.

### B.6 Chapman–Peled and the repository's `A_3` cone (source §7) — accepted

The source traces why `notes/TRUE_A3_METRIC_CONE_SYNCHRONIZATION.md` does not
supply the Chapman–Peled estimate.  The repository theorem gauges any edge
connection on the spherical building `A_3(F_q)` so that
`‖a·φ‖_(L^r(E)) ≤ 9‖K_φ‖_(L^r(T))`, with the constant independent of `q`, of
the length function, and of the dimension.  The building's cone is simply
connected, so the repaired object is a **pure gauge**: the estimate measures
distance to `B^1`.  Chapman–Peled need distance to `Z^1` on random complexes
whose fundamental group is deliberately nontrivial, where a genuine cocycle is
a flat connection with nontrivial global holonomy — exactly the data a repair
to `B^1` destroys.

This is the same obstruction the repository already recorded in another
language in `notes/TRUE_AUXILIARY_CONE_RADICAL_WITNESS_NO_GO.md`, where
radical membership forces the encoded paths closed on `1-o(1)` of the finite
base and the simply connected cone then kills the marked holonomy.

Accepted, and recorded as an obstruction claim killing the route that would
try to close `random-complex-linear-cocycle-stability` with the `A_3` gadget.

### B.7 Hull (source §8) — accepted, and worth a node here specifically

Hull's small-cancellation quotients are guaranteed **acylindrically**
hyperbolic; ordinary word-hyperbolicity survives only in the clause where the
input is already hyperbolic and the relators are chosen to preserve it.  Since
this graph reasons heavily with acylindrical hyperbolicity (the
Fournier-Facio skeleton, the defect routing, `common-quotient-onto-normal-subgroup`),
and one existing node even writes "(acylindrically) hyperbolic" of a
candidate, the distinction is worth an explicit obstruction node: routing a
known non-sofic or non-residually-finite group through Hull does not make it
word-hyperbolic, and acylindrically hyperbolic groups include groups
containing `ℤ^2`, which no hyperbolic group does.

### B.8 The sofic + stable ⇒ RF diagnostic (source §9) — no new node

The source's §9 is a correct reading of `sofic-stable-implies-residually-finite`
and of why it cannot be turned into a universal proof that hyperbolic groups
are residually finite (infinite sofic Kazhdan groups are not permutation
stable, and hyperbolic groups are not known to be sofic).  Both facts are
already carried by existing nodes; nothing new was added.

---

## C. One correction to an existing node's prose

`nonsofic-hyperbolic-group` says the demand for a non-sofic hyperbolic group
"equivalently" answers whether non-residually-finite hyperbolic groups exist.
The implication runs one way only: a non-sofic group is not residually finite,
but a non-residually-finite hyperbolic group need not be non-sofic (it might
be sofic and non-residually-finite, exactly as this repository's own literal
group `E` is).  The graph now carries the weaker demand as its own claim,
`non-residually-finite-hyperbolic-group`, with a route down from the stronger
one; the existing node's body was left untouched, and the distinction is
recorded in the new node's `distinct_from`.

---

## D. What this file does not claim

- No resolution of the open problem, in either direction.
- No assertion that Needham's or Oyakawa's papers are correct beyond what was
  read: their statements were read verbatim, their proofs were not audited.
- No assertion about the *relative* Oyakawa construction (Theorem 1.3), whose
  residual finiteness is untouched by §B.4.
- No claim that the four surviving targets (relative filling input, persistent
  `H^2` class, Rips kernel without finite quotients, Chapman–Peled estimate)
  are of comparable difficulty, or that any of them is more tractable than the
  original question.
