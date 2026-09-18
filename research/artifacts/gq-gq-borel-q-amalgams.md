# gq-borel-q: Borel subgroups and amalgam presentations of GL_n(Q) (2026-09-17)

Lane `gq-borel-q` of the GL_n(Q) swarm. Target: `gl-n-q-embeds-in-fp-simple-group`.
Question: do B_n(Q), BN-pair, Curtis--Tits or other amalgam presentations reduce the root,
and does embeddability in finitely presented simple groups survive these amalgams?

## 1. Verdict

No reduction beyond "a nontrivial homomorphism of the simple group PSL_n(Q) suffices".

- `gl-n-q-root-needs-only-nontrivial-psl-maps` (landed 32a6ec03f): PSL_n(Q) is simple and cofinal
  with GL_n(Q); SL_m(Q) = PSL_m(Q) for odd m. Faithfulness, kernel disjointness and passage to
  quotients are free. Open target in that form: `psl-n-q-maps-nontrivially-to-fp-simple-groups`,
  wired into the root by `gl-n-q-root-via-nontrivial-psl-maps`.
- `sl-q-local-amalgam-gluing-is-the-whole-problem`: SL_m(Q) is the colimit of its subgroups
  SL_I(Q), |I| <= 4 (every Steinberg relation of SL_m over a field involves at most four indices).
  So a compatible family of homomorphisms of the pieces into one group S is the same as a
  homomorphism SL_m(Q) -> S, and for odd m the same as an embedding. Gluing separately built hosts
  of the pieces is the whole problem, not a step toward it.
- `borel-two-q-is-units-times-aff-q`: B_2(Q) = Q^x x Aff(Q), so B_2(Q) is in B_A iff Aff(Q) is.
  B_(m+1)(Q) = Q^m x| (B_m(Q) x Q^x).

## 2. Why each amalgam route stops

| Presentation | Pieces | Why it does not reduce the root |
|---|---|---|
| Local Steinberg amalgam (|I| <= 4) | SL_2, SL_3, SL_4 over Q | colimit = SL_m(Q); gluing = embedding |
| Curtis--Tits (simple roots, rank <= 2) | SL_3(Q), SL_2(Q) x SL_2(Q) | same; every vertex angle is pi/2 in any host (commuting diagonal elements), sum 3pi/2 > pi, so no nonpositive-curvature developability |
| Tits rank-2 parabolic amalgam (m >= 4) | parabolics with GL_3(Q) Levi factors | pieces already contain GL_3(Q), i.e. the n = 3 case of the root |
| Minimal parabolics over B (m = 3) | P_1, P_2 containing GL_2(Q) Levi factors | P_1 *_B P_2 maps onto GL_3(Q) with nontrivial kernel (the building is a generalized triangle, not a tree); a host of the amalgam need not contain GL_3(Q) |
| Bruhat--Tits (all primes) colimit | integral lattice stabilizers | owned by gq-k2-q (`sl-n-q-is-colimit-of-lattice-stabilizers`) |

## 3. Permanence nodes compared

- `bh-embeddability-forces-decidable-edge-membership` (ii): embeddability is not closed under HNN
  extensions or amalgams over finitely generated edges in general. So no general permanence theorem
  can be quoted for the gluing step.
- `mixed-permanence-closures-collapse-boone-higman-to-base` and
  `finitary-permanence-closures-collapse-boone-higman-to-base`: their probe is a finitely generated
  simple FA group. SL_m(Q) is simple but neither finitely generated nor FA (a countable group that
  is not finitely generated acts on a tree without a global fixed point), so these results neither
  help nor forbid a gluing theorem for SL_m(Q).
- `boone-higman-closed-under-finite-direct-products` (OPEN) is the only product permanence needed
  for Borel-type splittings, and it is avoided inside B_A, where products are free.

## 4. What B_n(Q) contributes

B_n(Q) is a necessary stepping stone (B_n(Q) <= GL_n(Q)) and contains the named stepping stones
Aff(Q) (via B_2(Q) = Q^x x Aff(Q)) and U_n(Q). It inherits O1 (it contains (Q,+)) and O4
(BS(1,2) <= Aff(Q) and the Heisenberg group <= U_3(Q) are distorted). Its iterated affine structure
B_(m+1)(Q) = Q^m x| (B_m(Q) x Q^x) would reduce B_n(Q) to Aff-type steps only given a permanence
theorem for split extensions with divisible abelian kernel, which is not available. The standard
wreath-product embedding of N x| H needs finitely supported functions and fails here (Q^x acts on Q
with infinite orbits), so `permutational-boone-higman-closed-under-wreath-products` does not apply.

## 5. Sparks (not pursued)

- A rank-increase theorem "SL_3(Q) embeds in a finitely presented simple group ⇒ every SL_m(Q) does"
  would make the root equivalent to its n = 3 case. Amalgams cannot prove it (section 2). The only
  mechanism in sight is matrix-ring stability: a ring R ⊇ Q with M_k(R) ≅ R (Leavitt-type) gives
  GL_(3k)(Q) <= GL_3(M_k(R)) = GL_3(R). That is gq-ring-leavitt's line.
