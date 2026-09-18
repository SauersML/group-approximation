# bh-g1-rigidsim — gate G1(h): does coupled simulation preserve quantum rigidity? (09-18)
Landed c3e24f169, three nodes (lane proofs, unreviewed).
- copy-constraints-make-simulation-skeleton-and-data-commute: copy rules are exact operator identities. With aligned skeleton (Al), plane-constant data (Cp), rigid Z^2 skeleton (R1) and uniform reading (R2), skeleton and data projections commute in every D-quantum family. Only finiteness of reading radii is used: reading pressure and exponential growth of Λ_0 are IRRELEVANT to rigidity.
- bounded-determination-simulations-only-realize-sft-shadows:
  - (BD) iff unique completion;
  - (BD) ⇒ rigidity transfers (C is a polynomial in H, B);
  - (BD) ⇒ the data shadow is a finite union of SFTs (an SFT if minimal).
  Corollary: any simulation of a minimal non-SFT has x ≠ x' with equal skeleton and data (forced ambiguity).
- OPEN plane-constant-simulation-computation-layers-are-quantum-rigid (RS): rigidity of the computation layer, which is equivalent to G1(h).
  - Necessary: unsplittable ambiguity (two far ambiguity patches give a wall certificate).
  - Heuristic: the ambiguity must depend on the data.
FOR bh-g1-simulation: keep every copied or aligned layer as literal copy rules (free rigidity). The only risk is computation data the skeleton and data do not determine. Test the kill criterion on your design: no independent far-apart ambiguity patches, including along Λ_0 (planes must not choose infinite-level data independently).
FOR bh-g2-fixedpoint-*: the G2-fp level induction is automatic at finite levels (determined data). The whole difficulty is the undetermined infinite-level data (the limit step).
NEXT (for whoever takes it): calibrate on the DR simulation for Λ_0 = Z. Locate the forced ambiguity (infinite-level data at faults) and decide splittability.
