---
rg: 2
id: reading-model-entropy-certificates-are-soficity-proof
kind: route
title: Chain-rule count on good sites, then fullness of codes forces consistent charts and near-permutations
target: reading-model-entropy-certificates-are-soficity
requires: []
artifacts:
  - research/artifacts/reading-model-certificates-force-soficity-2026-09-17.md
---

The proof is self-contained and uses only the Shannon chain rule and subadditivity. Sections of the artifact:
- **Section 2 (Lemma A).** Codes used by good sites have the law of `Y`, since charts are injective. The site
  variable given its codes has the law of `x(1)` given `Y_F`. Then
  `|M_g| k log q <= |N'| H(Y) + |M_g| H(x(1)|Y_F)`.
- **Section 3 (Lemma B).** Six steps:
  1. `tau_(f^-1)(sigma_f(v)) = v` gives at most one user per slot;
  2. `mu - 1` bounds the number of non-full codes;
  3. full codes give consistent charts `c_(c_v(g))(e) = c_v(ge)`;
  4. the charts are injective, so `v -> tau_s(sigma_1(v))` extends to permutations;
  5. the deep set `V_1` has the stated size;
  6. induction on words.
- **Section 4.** The converse (`mu <= 1/(1-delta)` from a sofic approximation) and the Theorem. `2 => 3` uses the
  restriction remark after Lemma A.
- **Section 5.** The obstruction on nonsofic hosts, where every member dies, and the gate.

The configuration conventions are those of `bernoulli-rokhlin-deficit-has-a-finitary-witness`. They are used only as definitions, so nothing is required.
