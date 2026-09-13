# Unused established theorems and hidden solved claims: a census of the graph (2026-09-12)

Lane `ex-free-unused-power`. Everything below was computed on MSI. The Cairn
solver (`tools/cairn.py`, class `Graph`) ran over a `git archive` of main.
Nothing ran locally except `git grep`.

## 1. Counts (tip 8b4ce1d3f, 21:40 CDT)

| quantity | value |
|---|---|
| claims | 9,354 |
| routes | 9,611 |
| established claims | 7,789 |
| refuted claims | 183 |
| invalidated routes | 504 |
| established, non-root claims no live route requires, invalidating nothing, refuting nothing ("unused") | 3,047 |

Most unused claims are terminal steps of attack lanes: firewalls, no-gos,
reductions. Ranking them by the size of their established proof cone puts
internal nonhyperlinearity machinery first (Atlas, Hecke, Whitehead cells).
Filtering titles by famous classes and properties, and excluding lane jargon,
leaves the list in §4.

## 2. Hidden-solved sweeps

1. **Duplicate establishment.** A tf-idf similarity over title plus lead
   paragraph compared every non-established, non-refuted claim with every
   established claim. It gave 534 pairs of score ≥ 0.45 (top three per open
   claim). All pairs scoring ≥ 0.62 were read, and all pairs with a root on the
   open side. Only one is a genuine case: an import whose source had been read
   but which had no route (§3). Every other pair is a reduction, an
   equivalence, a converse, or a strict special case.
2. **Hidden refutation.** Similar pairs whose titles differ in polarity (not,
   no, fails, non-, never, cannot, counterexample, refutes) were read. None of
   the established claims refutes its open partner.
3. **Single missing premise.** 845 open claims are the only missing premise of
   some live route. Those within distance 3 of a root whose best established
   match scores ≥ 0.5 were read, together with all premises of routes directly
   into roots. Each is a genuine open problem, e.g.
   `fp-infinite-simple-amenable-group`, `hyperbolic-finite-residual-is-torsion-free`,
   `every-injective-ca-preserves-uniform-bernoulli-measure`,
   `degree-one-assembly-surjective-torsion-free`. Some are equivalent
   restatements recorded as such, e.g. the tester-host Rokhlin nodes.
4. **Routeless required claims.** 539 open claims are required by a live
   route but have no live route of their own. For each, the forward cascade
   (claims that would become established if it were) was computed. 158 of
   them cite theorem numbers or arXiv sources in their bodies. Those whose
   bodies say "Literature input", "source re-read", "verbatim", or "citation
   to import" were read (§3).

5. **Prose asserts establishment, graph does not.** This check ran at tip
   2dc316605, where the graph has 9,467 claims (7,888 established, 184
   refuted, 507 routes invalidated). 84 non-established claims either say
   "ESTABLISHED" in their lead or name a DERIVATION route. Breakdown:
   - 51 name a route that exists but is blocked on an open premise. The prose
     overclaims, but nothing is falsely established.
   - 13 more have live routes that are still blocked.
   - 18 have no route at all.
   - 1 names a route that was never landed:
     `near-weyl-covariant-channels-round` names
     `near-weyl-covariant-channels-round-proof`. Commit 5a14f7b29 added only
     the claim file.
   - 1 names a consumer route, not a producer
     (`binary-leavitt-two-label-difference-occurrence-cells`).

   The routeless group includes a Reynolds/Mersenne/Iwahori family, all
   unreachable from roots. The research files deleted by becc912bd were all
   restored: every research path it removed is present at 2dc316605. These
   gaps are therefore authoring gaps, not damage. One routeless claim has
   three established premises and a complete two-line argument,
   `sofic-linear-weakly-sofic-chain-has-a-strict-link`. Its route was landed
   (dc2f7ed4d4).

## 3. Finding: a missing citation route (landed c609c3bab4)

`gkp-free-generalized-wreath-soficity` imports Gao--Kunnawalkam
Elayavalli--Patchell, arXiv:2401.04945v3, Theorem 3.7 (free case). Its node
recorded a source re-read on 2026-08-31 but had no route. The theorem text
was re-extracted from the v3 HTML on MSI: Definition 2.1, Definition 3.2, and
Theorem 3.7 verbatim, including the "In particular" clause for free
generalized wreath products over sofic actions. The route
`gkp-free-generalized-wreath-soficity-citation` lands it.

A forced solve at the same tip gives 11 newly established claims, 0 lost,
0 new refutations, and 0 new invalidations:

- `gkp-free-generalized-wreath-soficity`
- `sofic-coset-action-makes-amalgam-double-sofic` (general theorem: if `H`
  is sofic and `H ↷ H/Γ` is a sofic action, then `H *_Γ H` is sofic and
  `L(Γ) ⊂ L(H)` is RE/C)
- `one-kun-thom-compressor-is-relatively-embeddable`
- `commuting-kun-thom-compressors-are-relatively-embeddable`
- `heisenberg-kun-thom-slice-is-relatively-embeddable`
- `opposite-transvections-are-first-nonore-relative-gate`
- `farey-tree-lift-hits-opposite-steinberg-cycle`
- `one-opposite-steinberg-relator-does-not-close-laurent-cycle`
- `two-coordinate-relators-leave-stable-laurent-k2`
- `stable-laurent-k2-has-minimal-three-symbol-packet`
- `torsion-symbols-exactify-by-corners-not-infinite-symbol`

Checked by this lane before landing:
- the difference-cocycle embedding of the double;
- the fold-kernel free basis;
- the Tietze rewriting of the one-compressor double;
- the separability and cyclic-extension steps of the commuting and Heisenberg
  telescope routes.

The Steinberg/K2 chain was skimmed only: it is algebraic K-theory
(homotopy invariance, Bass boundaries) that does not use soficity.

**Corollary (landed 3ca27ba509 as `free-group-doubles-over-any-subgroup-are-sofic`,
with the import `gkp-free-group-actions-are-sofic`; unreviewed).** GKP arXiv:2401.04945v3,
Theorem 2.19, verbatim: "Any action α : G ↷ X where G is a free group is
sofic." `gkp-sofic-action-toolkit` imports Theorem 2.14 and Propositions
2.15--2.16 from the same paper, but not Theorem 2.19. Theorem 2.19 is quoted
in `research/artifacts/gkp-2401-04945-verified.md` and cited inline by the
Mihailova routes (`mihailova-coset-wreath-sofic-action-boundary-proof`,
`mihailova-stabilizer-proof`), but no claim imports it. Combining Theorem 2.19
with the double theorem: for every subgroup `Γ` of a free group `F`, the
double `F *_Γ F` is sofic and `L(Γ) ⊂ L(F)` is RE/C. For finitely generated `Γ` this follows classically
(M. Hall separability makes the double residually finite). The new cases are
infinitely generated `Γ`, including normal subgroups with nonsofic quotient
`F/Γ`.

Other routeless imports have cascades of at most 1:
- `sinchuk-a1-invariance-for-a4-containing-types`;
- `purely-infinite-leavitt-path-v-monoid-cancellation`, marked "citation to
  import", with its sources not yet read.

The remaining marked nodes are genuine open claims that merely quote
literature: `vn-rank-galois-invariant-for-torsion-free-groups`,
`wreath-amenable-near-representation`,
`fpbs-fixed-price-countable-from-finitely-generated`,
`inner-tensor-agreement-is-amplification-stable`, and
`exel-loring-mark-quantization`, which calls itself a programme.

## 4. The most general unused theorems, and what they do and do not reach

1. `two-generator-fp-all-group-master-tester`: one 2-generator finitely
   presented `U` tests, for all groups at once, soficity, hyperlinearity,
   Farrell--Jones, Bost, Bass, the determinant conjecture, surjunctivity, and
   direct/stable finiteness. Consumers exist as fixed-host claims, such as
   `fixed-gottschalk-test-group-is-surjunctive` and
   `master-host-satisfies-determinant-conjecture`. It is a reduction only.
2. `hereditary-property-second-level-dichotomy` and
   `arithmetical-complexity-table-of-group-properties`: every hereditary
   property with a finitely presented counterexample is `Π⁰₂`-hard on
   enumerated codes. The open finite-presentation cells are each a
   Higman-embedding question for that property.
3. `division-ring-embedding-torsion-free-one-group-tester` and
   `kaplansky-torsion-free-direct-stable-master-tester`: torsion-free testers,
   reductions only.
4. `relative-hull-quotient-with-full-mf-radical`: every finitely presented
   torsion-free acylindrically hyperbolic `G`, with a finite `Ω ⊂ G`, has a
   quotient `P` injective on `Ω`. `P` is 2-generated, finitely presented,
   torsion-free, Kazhdan, and acylindrically hyperbolic, with `Res_MF(P)=P`.
   Derived here: finite quotients are MF representations, so `P` has none.
   By Malcev, every finite-dimensional linear representation of `P` over any
   field is then trivial, and `C*_r(P)`, `C*(P)` are not MF. It does not reach
   the hyperbolic roots: the quotients are acylindrically hyperbolic, not
   hyperbolic.
5. `leavitt-invariant-random-subgroups-are-trivial-mixtures`: every p.m.p.
   action of `L_(F_2)(1,2)^x` is free off its global fixed set. With
   nonsoficity, every nontrivial ergodic action is essentially free and
   nonsofic. It does not decide `leavitt-units-have-zero-rokhlin-entropy-supremum`.
6. `stw58-tracial-selfless-k-stability`: tracial selfless algebras are
   K-stable in all degrees. With the selflessness of `C*_r(F_n)`
   (Amrutam--Gao--Kunnawalkam Elayavalli--Patchell), this would give
   `π_k U(M_m(C*_r(F_n))) ≅ K_(k+1)(C*_r(F_n))` for all `k, m`. That is a
   nonnuclear slice of STW LVIII, not the root. The import of the
   selflessness theorem has not been checked by this lane.
7. `groups-containing-kun-thom-pair-have-nonsofic-actions`: needs an
   infranormal non-normal Kazhdan pair. `arithmetic-integral-subgroup-is-incompressible`
   rules out the arithmetic pair, so `sl3z-admits-nonsofic-action` stays open.
8. `fpbs-positive-cost-two-generated-nonamenable`: contrapositive, if every
   2-generated subgroup is amenable, every free action has cost 1. It does not
   settle `fpbs-bounded-exponent-bounded-finite-subgroups-price-one`, whose
   groups may contain 2-generated nonamenable subgroups.
9. Boone--Higman classes: `positive-char-surface-linear-groups-satisfy-boone-higman`,
   `global-field-soluble-linear-products-satisfy-boone-higman`,
   `virtually-free-by-cyclic-groups-satisfy-boone-higman`. The open
   characteristic-zero transcendental cases need hosts these do not supply.
10. `a2-action-with-non-finitely-presented-image`: answers
    Fournier-Facio--Wu--Zaremsky Question 5.8. No root represents that question.
11. `double-swap-involution-normally-generates-elementary-group`: one
    involution normally generates `EL_m(R)` for `m ≥ 4` and every nonzero
    ring `R`.

## 5. Bounded negative result

No unused established claim, alone or combined with one other established
claim, settles any of: `q3-4-resolved`, `non-hyperlinear-group`,
`gottschalk-surjunctivity-conjecture`, `determinant-conjecture`,
`boone-higman-conjecture`, an STW99 root, or an fpbs goal. The bound is the
sweeps of §2 plus manual reading of about 45 nodes. It is not a proof that
no combination exists.
