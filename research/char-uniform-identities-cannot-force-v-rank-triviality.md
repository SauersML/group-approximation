---
rg: 2
id: char-uniform-identities-cannot-force-v-rank-triviality
kind: claim
title: No rank argument whose ring identities already hold over a subring of C can force Thompson's V rank gate in positive characteristic
distinct_from:
  sofic-configurations-cannot-force-v-rank-triviality: that blocks arguments confined to sofic configurations, over any field; this blocks characteristic-uniform arguments over any configuration, through the von Neumann rank on C[V].
artifacts:
  - research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md
---

**ESTABLISHED** by `char-uniform-v-rank-firewall-proof` (artifact Section 3). Independently re-derived
by `w3-vf-linear`: PASS (Section 31.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`). Imported at statement level: the standard von Neumann dimension facts, namely that
the trace of the range projection is a Sylvester matrix rank function on `C[G]`.

**Setting.**
- `R ⊆ C` is a subring and `phi : R -> F` a ring map. An argument about rank functions on `F[V]` is *`R`-uniform*
  if every equality between matrix expressions it uses already holds in `R[V]`.
- Its other premises are the Sylvester axioms, and single-element conjugacy data `rk(q([g])) = rk(q([g']))` for
  `q` in `R[t]` and `g, g'` conjugate in `V`.

**Statement.**
1. **Von Neumann values** (Theorem 3.1). For `g` of order `n` and `q != 0`,
   `rk_vN(q([g])) = 1 - #{zeta^n = 1 : q(zeta) = 0}/n`. For infinite order the value is `1`.
2. **Firewall** (Corollary 3.2). No `R`-uniform argument concludes `rk(1 - [g]) < 1 - 1/ord(g)`, or that a rank
   function on `F[V]` is the augmentation rank.
3. **`p`-sensitivity** (Corollary 3.3). A proof of `thompson-v-ternary-rank-functions-are-augmentation`, or of its
   characteristic-two analogue, must use an equality that holds in `F[V]` and fails over the lifts. The basic
   example is `(1 - [s])^p = 0` for `s` of order `p`.
4. **Established tools** (Corollary 3.4). `rk_vN` satisfies the conclusions of the torsion law, the fixed-rank
   identification, uniform displacement, wandering freeness and the dichotomy. So none of them can be the decisive
   step.

**Consequence** (Corollary 4.1, with `sofic-configurations-cannot-force-v-rank-triviality`). A gate proof must use
a configuration not known to be sofic, or tuple-level conjugacy through outside conjugators. It must also use a
`p`-sensitive identity. The natural `p`-sensitive object is a clopen `p`-cycle with `p = char F`; see the open
`v-rank-order-char-cycles-are-trivial-plus-regular`.
