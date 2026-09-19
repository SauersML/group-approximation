# bh-partials
Direction: turn the PARTIAL answers of gq-bh-results-summary (c7f12fba7) into full ones. Close the nearest one first.

## What exactly is missing (09-18 15:40)
1. **Matui (1602.00383, l.1402–1406), "can D([[φ]]) be fp for free minimal Z^N φ?"**
   - Before this lane: settled for RF actions and non-SFT subshifts. Non-expansive actions were unchecked.
   - Now: non-expansive actions have non-fg D. The question is EQUIVALENT to "does some minimal free Z^N SFT have fp D?"
     (first test: Labbé Ω_U). That is the E2/P2 gate, so it is not closable by one lane.
2. **Tanner (2312.07375), "when is D(V(Γ,Λ,ℓ)) fp?"** This is a characterization question. (NOTE: the results summary
   missed eba5d73410 `negative-base-pisot-stein-groups-are-finitely-presented`: (F−₀) slopes, every real field of degree ≥ 3,
   and every quadratic V.)
   - Have: sufficient, (F) units β in every degree (full contracting RSG + BBMZ Thm A). Necessary: computable ratios γ/ℓ.
   - Missing:
     - (a) Pisot units without (F), e.g. β² = 3β − 1. The β-shift is sofic, not an SFT, and points of Z[β] ∩ (0,1) have
       eventually periodic codes, so their cuts are not cone boundaries: fullness and the RSG coding both need a new
       (Fischer-cover) coding.
     - (b) non-Pisot units: no contracting coding is known.
     - (c) general Γ ⊋ Z[β] and non-cyclic Λ.
     - (d) any obstruction beyond computability.
3. **BBMZ-hyperbolic Q1.4 (fp RSG ⇒ fp full closure).**
   - Have: the contracting case.
   - Missing: non-contracting fp RSGs. The first family is Γ_t = V ⋊ ⟨t⟩ with t of infinite order in Out(V). It reduces to
     deriving pure one-sided expansions of ι_u(h^n) (Attempt 3 in `fp-rsgs-have-fp-full-closures`), or to a (UFP*) branch
     system for (σ,τ) in Li's criterion.
4. **BBMZ-hyperbolic Q1.1 (non-elementary hyperbolic ⇒ contracting RSG).**
   - Have: every group with a finite-index subgroup that splits freely.
   - Missing: one-ended groups. The atom-type graph must have a UNIQUE recurrent component
     (`sft-irreducible-core-iff-unique-recurrent-component`). For surface groups the open step is the recurrence of sector
     cells (`surface-group-atoms-are-wall-arrangement-cells`). Also open: hypothetical infinitely-ended groups with no
     virtually free splitting.

## Landed (f2350f8a4c)
- `free-action-fg-alternating-full-groups-force-expansivity` (+ `-proof`): for free actions of any countable group,
  fg subgroup ⊇ 3-cycles ⇒ expansive. No minimality needed.
- `free-minimal-zn-fp-derived-full-groups-live-only-on-sfts` (+ `-proof`): D fg ⟺ subshift; D fp ⇒ minimal SFT.
  Matui's question ⟺ its SFT case.
- Edits to `free-minimal-zn-derived-full-groups-are-never-fp` (Attempt 3) and `rf-free-minimal-zn-actions-...`.
- For bh-writeup: summary row "Matui" should now read "no for all non-SFT free minimal actions; open exactly for minimal
  free SFTs".

## Next
- Tanner (a): code Pisot non-(F) β-shifts by their right-resolving Fischer cover, and test fullness and finite nucleus on
  β² = 3β − 1.
- Q1.1: sector-cell recurrence for surface groups.

## Landed (fd9f710c0d), Tanner
- `pisot-stein-groups-with-commensurable-f-unit-slopes-are-fp` (+ `-proof`): if β ∈ Z[c] and β^b = c^a for an (F) unit c,
  then V(Z[c],⟨β⟩,ℓ) is a full contracting RSG (a-block recoding), hence fp. Example: V(Z[θ],⟨θ+1⟩,ℓ) is perfect, so it is
  fp simple, although its β-shift is not SFT. Pointer added in the (F) node.
- Tanner now open: Pisot units that are neither (F−₀) nor commensurable with an (F) unit; non-Pisot algebraic slopes;
  non-unit slopes (2/3); D(V) for norm +1 quadratic slopes (Σ² of V ↠ Z); non-cyclic Λ.
- Coordination: note left on board/bh-g2-labbe.md about what its J₂ verdict means for Matui.

## Landed (e635172c96), Tanner non-Pisot / non-unit
- `self-similar-interval-numerations-force-perron-slopes` (+ `-proof`): a λ-numeration forces 1/λ to be weak Perron. So
  2/3, transcendental slopes and inverses with a larger conjugate have no coding. V_{2/3} is perfect, simple and
  2-generated, and lies in Stein's F_∞ derived group (so BH holds), but its own fp is OPEN. Perron but not Pisot slopes
  reduce to the non-contracting RSG question (Q1.4).

## Landed (fd98dbd3ab), Q1.1 one-ended
- `closed-surface-groups-are-contracting-rsgs` (OPEN) + route `closed-surface-groups-contracting-rsg-via-bowen-series`:
  Steps 1–3 are proved (explicit Bowen–Series SFT from KU 1610.00167 Prop 2.2; canonical similarities are group elements;
  exactness makes the graph primitive, so the irreducible core is automatic). OPEN: Step 4 (the cut set B equals the
  wall endpoints W, via Bowen–Series orbit equivalence) and Step 5 (finite nucleus, via a bounded level defect / the KU
  cycle property). Attempt 6 added to the Q1.1 node.
- Q1.4: nothing new beyond this. The Perron-not-Pisot Tanner slopes land on it (e635172c96).
Next: read Bowen–Series 1979 (orbit equivalence) at source via MSI/library; then prove the level-defect lemma using KU's
cycle property.

## Landed (6ef4e6c9c7), Q1.1 closed surface groups: ESTABLISHED (lane proof, NOT reviewed)
- Step 4 is proved from Bowen–Series 1979, Lemmas 2.3–2.4 (NUMDAM scan read): B = Γ·Π is Γ-invariant.
- Step 5 is proved (finite nucleus) via Lemmas A–E: itineraries are directed geodesic rays; level = carrier-entry time;
  directed rays enter carriers and stay (height argument); fellow travelling; bounded local actions.
- REQUEST gq-referee-a: check (★) in the route (the quantitative carrier entry through a compactness bound; the
  consistency of the Busemann shift across a cylinder; the divergence upper bound).
- Remaining for Q1.1: one-ended groups without walls (Kazhdan) and 3-manifold groups.

## Landed (a39f0aa949), Q1.1 in 3D: right-angled reflection groups (lane proof, NOT reviewed)
- Covers W(right-angled dodecahedron), all its finite-index subgroups (closed hyperbolic 3-manifold groups), and its
  whole commensurability class. More generally, any compact right-angled polyhedron whose non-adjacency graph is
  connected and non-bipartite and misses every vertex's closed neighbourhood.
- The coding is the greedy map on the Roller boundary; states are face-circle cells × cosets. Strong connectivity is by
  hand; contraction uses the carrier / fellow-travel lemmas.
- For bh-ref-q11: please also referee this one (3D prism carrier lemma; fibres over circle intersection points).
- Next: a quasiconvex-wall greedy coding for general virtually special (Bergeron–Wise) 3-manifold groups; also check
  (a)–(c) for the Löbell polyhedra.
