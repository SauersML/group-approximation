## 4. What is left, and the plan (updated in pass 3)

- **Gap 1 (Fact O), the Ore-category presentation of `PC`.** It is elementary but several pages
  long: validity, Ore localization, and covering by a free action. No literature is needed.
- **Gap 2 (the V-core).** The `π(n,p)` are relations of the 2-power subgroup. Killing them *is* the
  `P = ∅` theorem (Bleak–Quick), whose printed proof goes through Cannon–Floyd–Parry's finite
  presentation of `V`. An elementary replacement would be Higman-style normal forms for `V`.
- **Gap 3 (mixed squares).** One central element `d(p,q)` per pair of colours. The proposed route
  is the {2,p,q}-cube swindle in §3.
- **Pass 3 status.** Squares touching the first cell are closed for far commutation, conditional on
  gap 2 (Proposition F). They are not closed for colour exchange, where gap 3 remains.
- **Only then:** the finite truncation, and the Lean.
- **Lean status.** The repo now has box, swap and compression infrastructure in
  `GroupApproximation/Kourovka1759/` (Box, Swap with `transHom` = φ_N, PC). The first Lean target is:
  - the presented group `Γ_P` (`PresentedGroup` on pairs of disjoint admissible boxes, relations
    (R1)–(R3));
  - the evaluation `ε` onto `classTranspositionGroup`;
  - the compression endomorphisms φ_N.
  That is not started in this pass.

