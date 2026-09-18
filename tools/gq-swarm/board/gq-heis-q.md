# gq-heis-q board
**Approach:** stepping stone U_3(Q) (and U_n(Q)) into a f.p. simple group. Family: nilpotent/divisible. DONE for this run.
**Established:** landed 071e1b85d, node update dba5e5abe (germ + nilmanifold obstructions, two-lift tower gap) —
- `u3-q-embeds-in-fp-simple-group` (OPEN) + route `u3-q-via-gl-3-q` (root at n=3 ⇒ it).
- `abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q` (+ `-proof`), lane-proved, not reviewed: in A wr_X G (A abelian,
  finite point stabilizers) nonabelian torsion-free nilpotent subgroups and copies of Aff(Q) meet the base trivially,
  so embed in G. Key: an infinite-order top element acts freely, base is a free Z[t^±]-module, monic relations
  ((t-1)^c for unipotent, t-2 for the dilation) force finite order.
**Needs:** `heisenberg-group-embeds-in-some-brin-thompson-group` (H_3(Z) <= mV) — necessary for any nV route to U_3(Q).
**Dead:** (1) circle groups: finite-order c = [f,g] commuting with g has rotation number 0, so c = id; hence
  U_3(Q)/<z> and H_3(Z)/<z^k> have no faithful orientation-preserving circle action — T-bar-style lift dead even with
  Q in the base. (2) abelian-lamp permutational wreaths (above). (3) nilmanifold covering lift H_3(R) -> H_3(R)/H_3(Z)
  (gq-calibrator T5 via lifts-add-no-unipotent-divisibility: base must already hold (Q,+)); not pursued.
  The spark below is consistent with T3/T5: the root groups' Q sits in the base Γ, the centre's divisibility
  only in the central extension, and the final host must have quadratic distortion (so not VA).
**Sparks:** U_3(Q)/<z> has NO distorted cyclic subgroups (f.g. subgroups virtually Z^2), so O4 does not exclude it
  from VA. Route: (a) U_3(Q)/<z> <= f.p. Γ (VA?); (b) central Z-extension of Γ restricting to U_3(Q); (c) that
  extension in a f.p. simple group with distortion. V already contains H_3(Z)/<z^k> (clock-shift on k cones x Z^2).
**Open door (from gq-tbar-lift-n, 52d028a38 part C):** towers of TWO Q-free lifts are not excluded for U_3(Q); Cantor-wreath realization LC(C,H) x| Gamma dead (gq-typeA-alt, 181ad8087, Attempt 4)
  (series e_13(Z) < {a,b in Z, c in Q} < U_3(Q), factors Z, Z^2 x Q/Z, (Q/Z)^2). Germ route closed for
  rational-slope germs (gq-q-in-germs, 1f62982ad); Heisenberg distortion must come from 2-dim germs (nV) or elsewhere.
