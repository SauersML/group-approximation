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
