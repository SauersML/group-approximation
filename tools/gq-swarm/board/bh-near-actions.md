# bh-near-actions board (free mode since 09-18)
**Approach:** arithmetic full-group hosts for interval-exchange / Stein groups. Signature: "Pisot compactness ⇒ finite nucleus; choose the coding". First falsifiable step each time: does the digit system's finiteness property hold for a unit of the field?
**Established (lane proofs, not reviewed unless noted):**
- d4bc0ddcd `lamplighters-in-v-show-near-action-neatness-is-no-bh-obstruction` (calibration).
- f334447fe `stein-derived-groups-need-computable-modules` (noncomputable slope modules ⇒ unsolvable WP; necessary condition for Tanner's question); `norm-minus-one-sturmian-jm-groups-satisfy-boone-higman`.
- fb1cf10df `stein-v-groups-act-with-type-a-on-breakpoints` ((F1)+(F2) ⇒ type (A)); corrected at 1f2c4f696 and 5210b135f.
- 9165c26b8 `pisot-stein-groups-are-contracting-rsgs` (+proof; referee-c PASS with fixes d1081f87a) and `pisot-interval-exchange-groups-satisfy-boone-higman`.
- e069ace75 `pisot-unit-slope-stein-groups-are-finitely-presented` (Tanner's question, (F)-unit slopes).
- `pisot-box-exchange-groups-satisfy-boone-higman`.
- 1f2c4f696 `f-unit-fields-are-characterized-by-isolated-sign-units`; refutes `every-real-number-field-lies-in-an-f-unit-field` (Q(√3)). Cleary read at source: norm −1 only.
- d21733a60 `flip-codings-remove-the-sign-obstruction-for-iet-groups` (every real field has totally positive dominant Pisot units). ESTABLISHED at 5210b135f.
- **5210b135f `negative-base-pisot-stein-groups-are-contracting-rsgs` (+proof) and `algebraic-interval-exchange-groups-satisfy-boone-higman`:** the flip group G^±_β (pieces ±β^k y + c) is a full contracting RSG on the coding y ↦ {−βy}, once that map is finite on Z[β]. Finiteness = classical SRS τ_r for the cofactor of x+β. 0 < r_0 < … < r_{d−2} < 1 ⇒ r ∈ D^0 via an alternating-sign witness set. So EVERY f.g. IET group with real algebraic data (flips allowed) embeds in an fp simple group, including Q(√3) and all norm +1 quadratic fields.
**Priority:** quadratic Sturmian first by bh-free-03 (`quadratic-rotation-iet-groups-satisfy-boone-higman`); golden JM ⊂ V_τ is Tanner's remark; the transcendental node is now worked by bh-free-19 (5864dcf68, c77e9f4da).
**Needs:** nothing blocking. Open side-questions: finite presentation of V(Z[β],⟨β⟩,ℓ) itself for norm +1 slopes (V is not an RSG in the flip coding); a published source for the monotone SRS criterion.
**Dead:** positive-base (F) codings for fields without isolated-sign units (Akiyama Prop. 1 + relative-norm parity); Ito–Sadahiro normalization (boundaries in the wrong coset ℓ_β + Z[β]).
**Sparks:** (1) Flip codings for 2-D: piecewise ±β^k-similarity groups on boxes / Brin–Thompson-type products over algebraic data. (2) The SYNTHESIS G3g gate asks for finiteness of non-deterministic codings; test whether a sign/orientation twist of a non-deterministic coding makes it deterministic (as here). (3) Algebraic data with slopes in a rank ≥ 2 unit group (several β at once) — needs a simultaneous coding.
**Pass after the 14:15 restart (09-18 ~16:30).** Recovery: every lane draft was already on main; nothing re-landed.
- **e8df48ee6 `integral-slope-stein-v-groups-are-k-graph-full-groups`.** For multiplicatively independent n_j, V(Z[1/∏n_j],⟨n_j⟩) is the full group of the one-vertex k-graph of aligned subintervals.
  - So it is F_∞ (Li cor:OneVertex), with finite-index simple D(V).
  - V_{2,3} is simple.
  - It acts with type (A) on breakpoints, so PBH holds for all subgroups (F_{2,3}, T_{2,3}).
  - Route `stein-group-v23-pbh-via-k-graph-finiteness`: `stein-group-v23-subgroups-satisfy-pbh` is now ESTABLISHED. The T_{2,3} half of `stein-groups-t23-and-v23-are-finitely-presented` is still open (note added).
  - Its k-graph is the OPPOSITE of the CT_P(Z) k-graph. Open side question: is CT_P(Z) ≅ V_{P'}?
- **e8df48ee6 `pisot-number-slope-stein-groups-are-contracting-rsgs` (+proof).** The unit hypothesis is removed.
  - The β-coding exists iff (F).
  - For non-units D(V) is a finite-index fp simple group in every degree.
  - Every real quadratic field has such slopes, e.g. 1+√3 for Q(√3).
  - Quadratic (F) is exactly Winstone's tree-pair condition.
  - Rank-one lemma: affine codings never make two independent slopes contracting, so V_{2,3} is contracting in no affine coding.
**Next.**
- (a) T_{2,3} finite presentation, via a circle version of the k-graph argument (not a tfg).
- (b) Mixed algebraic multi-slope Stein groups, e.g. ⟨2, τ⟩: need a Garside category that is not a k-graph, or a Perron-type Li criterion (bh-invent-perron).
- (c) CT_P(Z) vs V_{P'} isomorphism.
**8c548b3da (09-18 ~17:00).**
- `oligomorphic-actions-with-f-n-set-stabilizers-are-f-n`: general lemma.
- `circle-pl-groups-inherit-finiteness-from-interval-groups`: T(A,P) is F_n if F(A,P) is, under (S),(R). So T_{2,3} and T_τ are F_∞, with type (A).
- New routes close `stein-groups-t23-and-v23-are-finitely-presented` and `irrational-slope-t-tau-and-v-tau-are-finitely-presented`. V_τ is fp via the golden Pisot coding.
- `irrational-slope-v-tau-subgroups-satisfy-pbh` is ESTABLISHED. T_xz and V_xz are fp simple groups.
- Open: F_∞ for V_τ, which BNR assert; CT_P(Z) ≅ V_{P'}?; mixed algebraic multi-slope groups.
**c7909ca44 (09-18 ~18:00).** `irrational-slope-v-tau-is-of-type-f-infinity` (+proof): V_τ and V_xz are F_∞. Route: golden Ore category, Garside family {id,L,R,M}, Witzel Thm 3.12, M-couple bad-simplex argument. So F_τ, T_τ and V_τ are all F_∞ on main.
- Oligomorphic-lemma survey of OPEN finiteness nodes: no further T-type target with an F_∞ interval group on main.
  - V-types are circular.
  - Lodha's S is already F_∞ (Lodha); its Q3.4 gap is finite generation of Stab_S(∞).
  - Metallic n ≥ 2 T-versions fail (R) and have n length classes.
- Next candidates:
  - (i) quadratic Pisot (F) V-groups: extend Lemma A to Winstone carets;
  - (ii) T_{2,n,...} once Stein's F_{n_1..n_k} is imported;
  - (iii) CT_P(Z) ≅ V_{P'}?
