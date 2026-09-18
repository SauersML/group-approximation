# gq-obstruction-miner board
**Approach:** obstruction-miner. Signature: "scaled rational lines: scale = similarity ratio". Done.
**Invariant found:** GL_n(Q) (n>=2) contains a SCALED RATIONAL LINE: D ≅ (Q,+) scaled by every a in Q^x (incl. -1).
  Additive half (divisibility) is escapable via torsion (BHM); multiplicative half is not: torsion acts on D by ±1.
  Every dead family has a multiplicative invariant with f.g. value group (slopes, similarity ratios, denominators,
  end-germ slopes) that the scaling must factor through ⇒ finitely many primes ⇒ no Aff(Q)/SL_2(Q)/GL_n(Q).
  Also: every homogeneous quasimorphism vanishes on a scaled line; every element of it is exponentially distorted.
**Established (c8e0b926e, not independently reviewed):**
  - pl-quasi-similarity-groups-scale-rational-lines-by-ratio (+ -proof): in a periodic PL quasi-similarity group
    (T-bar, <T-bar, x->2x> which is f.p. and contains Q and BS(1,2), Stein-type lifts + dilations, x->-x), any
    element normalizing a copy of Q scales it by its similarity ratio c(t).
  - fg-pl-quasi-similarity-groups-contain-no-gl-2-q (+ -proof): f.g. such groups contain no Aff(Q), B_2(Q),
    SL_n(Q), PSL_n(Q), GL_n(Q), PGL_n(Q); orientation-preserving ones contain no Aff(Q), GL_n(Q) at all.
  - artifact research/artifacts/gq-gq-obstruction-miner-invariant.md (table of which half kills which family,
    the gate, calibration tests T-scale / T-sign / T-qm).
**Established (de04f7a2a, G1 verdict):** sl-n-q-lacks-property-fw (+ -proof): every countable non-f.g. group lacks FW/FA
  (coset-tree oriented-edge commensurated subset), so SL_n(Q), GL_n(Q), Aff(Q), U_n(Q), Q lack FW for all n>=2; for n>=3
  SL_n(Q) = union of Kazhdan SL_n(Z[1/m!]). Critic G1 route dead; level-by-level: SFT Thompson groups (incl. V_(d,r))
  contain no GL_n(Q), n>=3; RN vertex groups must virtually contain every SL_n(Z[1/m]). Open: uniform-defect version.
**Gate (what survives):** a host scaling one rational line by every prime WITHOUT a f.g. "ratio" invariant.
  Sharpest open test: is there a rational line in 2V (Kojima–Sheng Q ≤ nV) scaled by 3?
**Dead:** —
**Sparks:** (1) TAKEN by gq-deep-va-1 (3bac6e2a6, 9abe3b8d7): minimal copies of Q x|_2 Z in <T-bar, x->2x> excluded; blown-up case open in t-check-contains-q-rtimes-2-z. (2) End-germ version: f.g. PL groups
  with affine end-germs have translation parts in a f.g. Z[P]-module (Krull ⇒ no divisible elements) — sketch in artifact §5.
