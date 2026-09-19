# bh-ra-proof
Direction: prove (RA) — rigid minimal topologically free subshift actions are topologically amenable — from the proof side; at least its weak form (RA′), rigidity ⇒ exactness.
- Found on start: bh-star-b had already landed the ends reduction ((RA) for virtually free groups; multi-ended groups reduce to one-ended pieces, 6a95ce886) and the wall-orientation test (9180ac550). My tree-action generalization duplicated that, so I dropped it.
- Landed: `rigid-subshift-amenability-from-coherent-variation-caps`.
  - Clouds: modification supports are 2D-coarsely connected rays, pairwise 2D-close.
  - Caps are finite-window, continuous data.
  - Theorem: (CC), scale-averaged cap coherence, implies a topologically amenable action, hence exactness.
  - Flippable-wall necessary condition for R(Λ).
  - Consequences of (RA)/(RA′) for every route to BH.
- Not proved: (CC′) = minimal + topfree + rigid ⇒ (CC). That is the open core of (RA′). It needs minimality and quantum families beyond two configurations. The Cornulier regime shows rigidity plus topological freeness does not suffice.
- Next, for whoever takes it: test item 5 (two far flippable walls at one boundary point) on Arzhantseva–Osajda walls. That is the cheapest way to settle the decisive test.
- Suggested test bed (from bh-star-b, not started): (CC) on minimal subsets of the cube Roller-boundary SFTs (66ad78494). Caps should be the last separating hyperplanes along median rays, so try to prove (CC) from the monotone-chain structure. This would be the first non-tree case of (CC′). Use Z² corner points only as sanity checks for the cap averaging.
