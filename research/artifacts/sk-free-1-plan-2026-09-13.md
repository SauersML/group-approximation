# sk-free-1 plan: exactness of infinite simple Kazhdan LEF groups (2026-09-13)

Lane sk-free-1, a free lane in wave 10. I chose the problem after surveying main (tip bf95c23216).

## Survey (not duplicated)
- **Other free lanes:**
  - sk-free-2 and sk-free-7: stable rank one of R_X and bounded generation of G_X;
  - sk-free-3: the conjugacy problem;
  - sk-free-4: finite simple shadows and the boundary theorem;
  - sk-free-8: non-uniform exponential growth.
- **Existing nodes:** `subshift-elementary-groups-are-not-uniformly-simple`, fixed price one (`fpbs-*`), (TT)/T rigidity (`property-tt-mod-t-rigidity-for-elementary-groups`), character rigidity, the separable-factor count.
- **Live lanes:** C*-simplicity (sk-cstar-simple, -2), isomorphism rigidity, the sofic host, the f.p. sofic host, the decidable host.
- **Nothing on main decides exactness** (Yu's property A, equivalently exactness of C*_r) for G_X or for the hosts of Corollary 2 (LEF iff subgroup of an infinite f.g. simple Kazhdan LEF group).

## Choice
Exactness is the operator-algebraic property a reader of Brown's question asks about next: C*_r(G) exact, and the C*-side contrast with L(G) ⊂ R^ω.

**E1 (target, expected to close quickly).** Some infinite f.g. simple Kazhdan LEF groups are not exact.
- Route: Osajda (GAFA 2018) gives f.g. residually finite non-exact groups. RF gives LEF, so Corollary 2 (rev3, three PASSes) puts such a group Γ inside a host G. Exactness passes to subgroups (Kirchberg–Wassermann), so G is not exact.
- Consequences to state carefully: C*_r(G) is not exact, while L(G) embeds in R^ω. BKKO gives unique trace (trivial amenable radical). Whether Γ's box space / coarse expanders transfer: record, do not overclaim.
- Sharper form: if Osajda's groups are recursively presented, the universal host of `sk-universal-lef-host-b` Theorem C (if it PASSes) is itself not exact. This needs a check of computability in Osajda's construction.

**E2 (deep target, open).** Is G_X = EL_3(LC(X,F_2)⋊Z) exact for every infinite minimal subshift X?
- A yes gives exact C*_r(G_X), and a sharp dichotomy with the hosts of E1, alongside the SL_3(Z) obstruction.
- A no (a non-exact subgroup in some GL_m(R_X)) would be a much stronger statement than E1.
- Approaches:
  - (a) Tate-space picture: G_X acts on F_2((u))^3 by filtration-bounded F_2-linear automorphisms. Lattice stabilizers meet G_X in locally finite groups (SL_3(LC(X,F_2)) at the standard lattice). Look for a property-A orbit geometry.
  - (b) An amenable action of G_X on a compact space from the orbit representation.
  - (c) Embeddings of RF non-exact groups into GL_m(R_X) through banded finite models (sk-lef-embedding-d), or an obstruction via Krylov counts (sk-sl3z-bandwidth).

## Deliverables
- **Nodes:** grep before authoring. E1 claim + proof route, citing Osajda at source with verbatim theorem text fetched on MSI; E2 open claim with Attempts.
- **Artifact:** `research/artifacts/sk-free-1-exactness-2026-09-13[-partK].md`.
- **Proposal:** at most 3 lines after Corollary 2, only after E1 PASSes. Claims queued in `$SK/queue/sk-verify-13.txt`.
