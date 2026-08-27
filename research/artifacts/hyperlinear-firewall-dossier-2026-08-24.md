# Hyperlinear-vs-sofic firewall dossier — ingestion audit, 2026-08-24

External dossier ("I do not have a valid proof of either `Hyperlinear ⊆ Sofic`
or its negation … what is now proved is a fairly rigid firewall around any
eventual answer"), five sections. This file records the disposition of each
section: what was already in the graph, what was newly wired, and what was
declined.

The dossier's own headline is honest and is **not** a program result: it
claims no resolution of Question 3.4. Nothing below establishes or refutes
`hyperlinear-nonsofic-group`, `hyperlinear-implies-sofic`, or the program goal
`non-hyperlinear-group`.

## §1 — Bounded-dimensional hyperlinearity collapses to LEF

**Already in the graph, essentially verbatim.**  The dossier's theorem and its
proof (compactness in `U(d)^F`, Mal'cev residual finiteness of a finitely
generated linear group, one finite quotient separating the finitely many
`V_x^(-1)V_y`, left-regular action giving normalized Hamming distance `1`) is
`exact-finite-dimensional-group-table-classicalizes` together with its route
`exact-finite-dimensional-group-table-classicalizes-proof`.  That route's
closing paragraph already carries the compactness corollary and the sentence
that a genuine gap "forces the required dimensions to escape every finite
bound".  No duplicate was authored.

**Newly wired:** the *group-level* consequence, which the graph did not state
and which nothing consumed the table claim for.  `bounded-dimension-microstates-force-lef`
quantifies over all finite windows of a group and over approximate solutions,
concludes LEF and hence soficity, and records the contrapositive `(BDM4)`: a
hyperlinear nonsofic group must have a window whose minimum microstate
dimension diverges.  Its route spends the dimension cap at the pigeonhole and
compactness steps, then calls the table claim, then reads off LEF and imports
LEF ⟹ sofic (Gordon–Vershik; Elek–Szabó; Weiss).

One correction to the dossier's framing: it states the separation hypothesis
as `‖U_x − U_y‖_2 ≥ c` without saying that `c` must not shrink with the defect
`δ`.  If `c` is allowed to depend on `δ` the compactness step fails and the
theorem is false as stated.  The node states the uniformity explicitly and
notes it is automatic (with `c = 1`) on the regular-character face.

## §2 — Quantitative divergence for the central-phase route

**Newly wired, and the strongest new item in the dossier.**
`central-phase-certificate-forces-divergent-filling` plus its `-proof` route.

Re-derived independently before authoring:

* `N = ⟨z^{b_1},…,z^{b_ℓ}⟩` is central hence normal, `E/N` is a genuine finite
  quotient of `P`, and residuality of `w` gives `z^a ∈ N`, i.e.
  `a ≡ Σ c_j b_j (mod m)`.
* `|e^{2πia/m} − 1| = 2 sin(π|a|_m/m)` with `π|a|_m/m ∈ [0,π/2]`, so
  `|a|_m ≥ (m/π)·arcsin(η/2) = κ(η)m`.  Note `η ≤ 2` always.
* `|·|_m` is subadditive and absolutely homogeneous over `Z`, giving
  `|a|_m ≤ εm Σ|c_j|`.
* Hence `Σ|c_j| ≥ κ(η)/ε`.

Two scope points the node makes that the dossier does not.  The hypothesis
used is `w ∈ R_fin(P)` (the finite residual), which is weaker than
`w ∈ Rad_sof(P)` and therefore gives a stronger theorem; the node includes the
one-line argument that sofic-radical words lie in `R_fin(P)`.  And the bound
is vacuous for `ε ≥ κ(η)` — it is a statement about the small-phase regime
only.

**Declined: the Clifford paragraph of §2.**  The dossier asserts "Since `r`
itself lies in the finite/sofic radical, `x ∈ [P, R_fin(P)]`" for `r = [k,h]`,
`x = [k,r]`.  What `kun-thom-clifford-radical-phase` records is that Kun–Thom
centralizer normalization puts **`x = [k,r]`** in `Rad_sof(H)`; it does not put
`r` there, and radicals being normal does not propagate membership downward
through a commutator.  In the Clifford crossed product `r ↦ c_Γ c_{hΓ}`, which
is not `±1`, so there is no evident reason for `r` to be radical.  The
conclusion drawn from it — that the fixed-coefficient commutator theorem
applies to `x` and forces the Clifford detector to be noncentral before the
final commutator — is therefore unsupported as written and was **not**
encoded, in either a claim or an `invalidates:` key.  If the intended premise
is different (e.g. a different `r`), it should be re-stated before wiring.

## §3 — The relative wall exists, but in a semifinite algebra

**Already in the graph, in more detail than the dossier gives.**  See
`kun-thom-clifford-relative-wall`, whose recorded dead end 3 ("Semifinite
comparison") is exactly the dossier's observation: in the tracial ultraproduct
the Jones projection and the compressor unitary do not lie in a common finite
algebra, `Ad π(t) = u_t J u_t J` leaves the basic construction, and only the
index invariant survives — which is why `[M:N] = ∞` is the surviving necessary
condition rather than a contradiction.  The route `clifford-ce-gives-bare-wall`
already records that the bare wall exists unconditionally in the Clifford
crossed product, i.e. the dossier's "the algebraic wall already exists exactly;
the missing operation is finite-trace compression without destroying it".  The
infinite-index/non-coamenable point is `commutator-compressor-carries-no-wall`
and `compressor-growth-index-homomorphism`.  No node authored.

The dossier's property-(T) paragraph (an exact finite-dimensional actor almost
commuting with a Kazhdan generating set is close to the commutant, so it cannot
carry the wall) is the same shape as
`parity-headed-compressor-kills-mark-in-exact-matrix-models` and
`kazhdan-asymptotic-commutant-transport`, both established.  No node authored.

## §4 — The one-compressor tower is exactly solvable at the HS level

**Conclusion already established twice** — by permanence
(`ascending-hnn-cannot-create-nonhyperlinearity`, via ABFG Corollary 1.1) and
by soficity of every one-compressor coset action
(`kun-thom-single-compressor-sofic-joint-nonsofic`).

**Newly wired:** the explicit construction and its rate, which neither existing
route supplies.  `one-compressor-covariance-has-free-hs-telescope` gives the
`L`-block telescope `Π_L(γ)|_{H_j} = ρ(α^j(γ))` with cyclic block shift, and
the dimension-free bound `2/√L`.  Re-derived: the shift is exactly covariant
on `L−1` blocks and wrong only at the wrap (`ρ(γ)` against `ρ(α^L(γ))`); one
block of dimension `d` inside total dimension `Ld` gives
`‖·‖_2² ≤ 4d/(Ld) = 4/L`.  The estimate is a block count, so `d` cancels.

The node states the scope limit the dossier leaves implicit: this models the
*relation*, not the group, and separates nothing, so it does not prove any
group hyperlinear on its own.

## §5 — The MF shortcut and its failure mechanism

**Newly wired as a hole plus a payoff edge.**
`reduced-amalgam-canonical-trace-is-mf` (open, four recorded attempts) and
`hyperlinear-nonsofic-from-mf-amalgam-trace` (route into
`hyperlinear-nonsofic-group`).

Corrections and sharpenings relative to the dossier:

* The dossier writes the nonsofic object as "the appropriate examples" of the
  symmetric double.  The graph has the exact statement: Kun–Thom v3 Theorem A
  covers the group double `G *_Γ G` directly, imported as
  `kt-pair-group-double-is-nonsofic` (2026-08-22).  **No existing route
  consumed that import**; this edge is what makes it usable on the flexible
  side.
* The negative half of §5 was already recorded, and more precisely:
  `shulman-symmetric-double-has-no-stable-trace-upgrade` establishes that
  arXiv:2603.13564v2 contains no trace upgrade, identifies Theorem 10 as an
  operator-norm algebra statement, and identifies the nearby genuine trace
  theorem (arXiv:2508.00125 Cor 35) together with the reason its domination
  arrow points the wrong way for a double.
* The route body states plainly that its prerequisite is *stronger* than the
  conclusion, so the edge is uphill.  It is recorded anyway because the
  strengthening is where Shulman's machine already reaches (the algebra-level
  result is established as `symmetric-double-weak-mf`), whereas the weaker
  "τ is a hyperlinear trace" version is a restatement of the target — the
  epistemic trap this graph names explicitly.  That rejection is recorded as
  Attempt 3 of the open claim rather than left implicit.
* The rank-one example `U_n = diag(−1,1,…,1)`, `‖U_n − I‖ = 2`,
  `‖U_n − I‖_2 = 2/√n`, is kept as the recorded reason the upgrade is not
  formal.

## Invalidations: none added

The dossier's closing box ("a negative solution cannot be bounded-dimensional,
compact, finite-quotient, ordinary relation-module, or one-compressor") reads
as a set of kills.  No `invalidates:` key was written.  Each of the new
established claims is a *necessary condition* on flexible-side constructions,
and turning one into a kill requires identifying a specific route in the graph
whose construction provably has the excluded shape — which none of the three
new claims does on its own, and which was not verified here.  Per the recorded
dead-route trap, an unverified `invalidates:` is worse than none: it either
sits inert or silently kills a live lane.

## Net

Nodes added: 4 claims (3 established, 1 open) + 4 routes.  Program status
unchanged: `hyperlinear-nonsofic-group` remains open, `non-hyperlinear-group`
remains the goal, and no route above closes either.

## Status of the three new established claims

All three are **recorded constraints**: they compile as established via their
own direct-proof routes, and no route consumes them as a prerequisite. That is
deliberate, not unfinished wiring. Each states a necessary condition on
flexible-side constructions, and the only rg:2 encoding that would make such a
condition load-bearing is an `invalidates:` key — declined above for want of a
verified target route. A later session that identifies a specific live route
whose construction is bounded-dimensional, or whose central certificate has
uniformly small relator phases with bounded filling, can turn the matching
claim into an obstruction by adding the key there.

## Verification run

`cairn check` against the live tree with the region in: **exit 0, 0 errors**.
`cairn why` confirms each of the three new claims established via its own
`-proof` route and nothing else; `hyperlinear-nonsofic-group` and the program
goal `non-hyperlinear-group` both remain **OPEN**; the new hole reports its
chain as `q3-4-resolved -> hyperlinear-nonsofic-group ->
reduced-amalgam-canonical-trace-is-mf`. No duplicate warning names any node of
this region. `research/FRONTIER.md` was **not** regenerated with this landing:
the shared tree carries two peer lanes' uncommitted work, and regenerating from
a dirty tree would bake unpushed peer nodes into a tracked generated file.
