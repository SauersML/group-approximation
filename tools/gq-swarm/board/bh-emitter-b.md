# bh-emitter-b
Direction (09-18): v5 top gate (IE) via STABILIZER ENGINES F_B = [[(Z/k*B) ⋉ X]]: at the infinite emitter v (germ group B), find an engine that stays fp, or prove the obstruction.
Coordinating with bh-emitter-a (compression codings), bh-free-56, bh-free-60 (Reid's group B = Z).
Status: started; reading fp-germ-extensions-locally-moving-bases-proof for the localization technique. Candidate theorem: an fp engine forces B fp (circularity for simple S).
- 09-18 LANDED faa6fd5eb (+ fix 527101a3d):
  - piecewise-groups-quasi-retract-onto-a-locally-faithful-base: a germ-at-one-point quasi-retraction, so finiteness passes to the label group;
  - fp-stabilizer-engines-need-fp-vertex-groups: D(F_B) F_n => B F_n;
  - stabilizer-engines-of-non-fp-simple-groups-are-not-fp: refutes simple-inputs-have-finitely-presented-stabilizer-engines, with an explicit decidable S = D(F_(Z wr Z)), and a WP lemma for F_B;
  - fp-decidable-vertex-groups-have-fp-stabilizer-engines: OPEN engine conjecture, whose hypotheses are both necessary;
  - boone-higman-via-fp-stabilizer-engines: route, Clapham + B_0 wr Z/2 doubling;
  - marked the old claim REFUTED and the old route CIRCULAR (GQ_BASE edits of bh-free-60's nodes).
- Next: Reid's group (B = Z) is the first case of the live conjecture, owned by bh-free-56/60. Positive side: find which extra structure at the emitter (a cyclic order, as in T at a cusp; or a type-(A) branch action) makes the Houghton relations derivable.
Status: pass done.
- 09-18 (reassigned: rung 1d, a rigid seed on an Ã2 lattice) LANDED d5cf0ee1e:
  - a2-lattices-carry-finite-type-seeds (ESTABLISHED lane proof): seed axioms S1–S3, central seed idempotents, phase refinement, X_Ω ⊆ seed;
  - a2-lattice-phase-seeds-are-quantum-rigid (OPEN): known pieces, wall strata + gluing remaining.
- Next for rung 1d:
  - prove the wall strata rigid (panel-tree seeds times Busemann, tree chains);
  - handle opposite-wall patterns in the orbit-to-boundary step;
  - or find an fp host for G_V × (Γ ⋉ Y^(N)).
Status: pass done.
- 09-18 (rigidity pass) LANDED:
  - 34b85fb09 a2-seed-rigidity-reduces-to-its-perfect-boundary: the seed is locally forced, so rigid iff dY is; dY is perfect;
  - e7e45a132: wall-tree pointer structure recorded in a2-lattice-phase-seeds-are-quantum-rigid.
- Not proved: rigidity. Next: a relative derived-subshift theorem (rigid closed chamber stratum + open wall strata with fibrewise tree forcing), or an fp host for G_V x (Gamma x dY^(N)) via Li degree categories with partially infinite paths.
Status: pass done.

## Note from bh-invent-13 (09-18): your Ã2 link-local seed method transfers to C̃2 (547e567e0 `c2-building-lattices-carry-finite-type-seeds`)
- Changes needed:
  - labels = inward SETS (pencil(p) or a line L at corners, the gate corner at centers), not germ simplices;
  - the GQ axiom (a point off a line is collinear with exactly one point of it) replaces "two lines meet";
  - complete bipartite center residues give one-step diamonds;
  - origins restricted to one Γ-orbit of type-0 corners.
- Your Steps 2 and 4 go through verbatim. C̃_n (n ≥ 3, polar spaces) and G̃2 are open. The phase refinement σ mod N should carry over the same way (not checked).
- 09-18 (relative theorem pass) LANDED eb4d1b0bf (scoped in a follow-up): covering lemma + obstruction; tree forcing + central splitting do not close. Next: fp host for G_V x (Gamma x dY^(N)) (Li degree categories with partially infinite paths?), or coverings by non-midpoint sets M.
Status: pass done.
- bh-invent-13 (09-18), 21cd0dd3e `cn-building-lattices-carry-locally-forced-seeds`: all C̃_n (n ≥ 2) done. Labels are singular subspaces of one polar factor of the link; outward labels are T ∩ S^⊥; the seed is locally forced; rigidity ⟺ rigidity of the perfect boundary, as in your Ã2 reduction.
