---
rg: 2
id: stationary-vershik-maps-generate-contracting-rsgs
kind: claim
title: The Vershik map of a stationary properly ordered Bratteli diagram with strongly proper read substitution is rational, and together with the Thompson group it generates a contracting rational similarity group
distinct_from:
  contracting-rsgs-embed-in-fp-simple-groups: that is the BBMZ host theorem; this verifies its hypotheses for one new family of generators, Vershik maps of substitutions.
  hyperbolic-groups-embed-in-contracting-rsgs: that places hyperbolic groups in contracting RSGs through horofunction boundaries; this places the minimal (measure-preserving, amenable-orbit) Vershik map of a substitution in one.
artifacts:
  - research/artifacts/gq-bh-bh-refute-verify-substitution-full-groups.md
  - research/artifacts/gq-bh-bh-free-03-substitution-full-groups.md
---

**Adversarial check (2026-09-18, lane `bh-refute`): PASS, conditional on the cited imports** (BBMZ, DHS and, for the IET node, Sturmian substitutivity), which it did not re-read. Report: `research/artifacts/gq-bh-bh-refute-verify-substitution-full-groups.md` (98821f68e). It re-derived the germ normal form, the no-stacking induction, the `T^{-1} c T` depth-shift transport, the finite nucleus, the full closure and the IET embedding, and found no gap. This is an internal check, not a referee review. The product and box-exchange nodes were not covered.

**ESTABLISHED** by `stationary-vershik-maps-generate-contracting-rsgs-proof` (lane
proof, elementary; internally checked by `bh-refute`, no referee review).

**Setting.** Let `sigma` be a substitution on a finite alphabet `A` that is primitive,
has `|sigma(b)| = L_b >= 2` for all `b`, and has letters `l, r` with
`sigma(b)_1 = l` and `sigma(b)_{L_b} = r` for all `b`. Let `Gamma` have nodes
`A ⊔ {rho}`, one edge `r_a : rho -> a` for each `a`, and for each `b in A` and
`1 <= i <= L_b` an edge `(b,i) : sigma(b)_i -> b`. Order the edges with a common
terminus `b` by `i`. Let `E = C_rho` (all infinite paths from `rho`); this is the path
space of the stationary Bratteli diagram whose read substitution is `sigma`. Let
`T : E -> E` be its Vershik map. Let `Sigma_Gamma`, `V_{Gamma,E}`, `R_{Gamma,E}`,
local actions and nuclei be as in `contracting-rsgs-embed-in-fp-simple-groups`.

**Claim.**
1. `Sigma_Gamma` has an irreducible core (the subgraph on `A`), and `T` is a
   rational homeomorphism of `E`: `T in R_{Gamma,E}`.
2. `T` is a canonical similarity near every point except the maximal path `x_max`,
   and `T^{-1}` near every point except the minimal path `x_min`.
3. `G_0 = <V_{Gamma,E}, T>` is a contracting RSG. More precisely
   `Nuc_{G_0} ⊆ {id_{C_u} : u in A} ∪ Nuc_T ∪ Nuc_{T^{-1}}`, a set with at most
   `3|A|` elements.

The key point is that no canonical similarity carries `x_min` to `x_max` (their
tails differ), so in any product of generators the singular germs of `T` and `T^{-1}`
never stack; when a `T^{-1}` meets a `T`, the intervening depth shift cancels to a
canonical similarity.
