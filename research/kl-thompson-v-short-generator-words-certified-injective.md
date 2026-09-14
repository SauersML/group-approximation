---
rg: 2
id: kl-thompson-v-short-generator-words-certified-injective
kind: claim
title: Exact injectivity certificates for the length-six and length-seven generator words over Thompson's V
distinct_from:
  kl-holds-over-thompson-v: that is injectivity for every nonsingular word over V; this is one exhaustive finite slice, words of variable length six or seven with Bleak--Quick generator coefficients, certified word by word.
  kl-four-same-sign-corner-words-inject: that is the general weight theorem over any group; this applies items 1 and 2 of it, the length-five theorem, coefficient localization and exact retractions onto V to every word of the census, and records which words are certified.
artifacts:
  - research/artifacts/kl-thompson-v-generator-census-2026-09-13.md
---

Let `V` be Thompson's group with the Bleak--Quick generators
`a = (00 01)`, `b = (01 10 11)`, `c = (1 00)`, and put `B = b^(-1)`.

**The census `W`.** Take cyclically reduced words

```text
w = g_0 t^(e_0) g_1 t^(e_1) ... g_(n-1) t^(e_(n-1))
```

with:
- every `e_i = +-1`;
- variable length `n in {6, 7}`;
- degree `0 < sum e_i < n`;
- `g_i in {a, b, B, c}` when `e_(i-1) != e_i`, and `g_i in {1, a, b, B, c}` otherwise.

Words are identified up to rotation and `w -> sigma(w^(-1))`, where `sigma : t <-> t^(-1)`.

**The claim.** `W` has `181202` classes. For `85432` of them the coefficient map
`V -> (V * <t>)/<<w>>` is injective. Each certified class carries one of these
exact certificates:

| certificate | classes |
|---|---|
| FINITE: the coefficients generate a finite subgroup | 63678 |
| R4: at least four light same-sign corners | 4380 |
| POWER: a proper power of a word of variable length at most three | 6 |
| CORNER3: exactly three light corners, with (D4) and (A2) holding in V | 15204 |
| RETRACT: an exact retraction `V * <t> -> V` killing `w` | 2164 |

The other `95770` classes carry no certificate. They are listed by class in the
artifact.

## Scope

- **Not a proof of KL over V.** It does not decide
  `kl-holds-over-thompson-v`, and it does not decide
  `kl-violating-equation-over-thompson-v` even on the frontier.
- **The collapse run adds nothing here.** All `113144` words left after FINITE and
  R4 were run through Todd--Coxeter enumeration over `<t>` at a coset budget of
  `200000`. None collapsed V, but an overflow certifies nothing, so that run is
  recorded only in the artifact and in the Attempts of the violation node.
- **Weaker certificate classes.** A word certified by RETRACT has a solution in V
  itself, after a diagonal embedding. POWER and CORNER3 rest on the curvature and
  citation theorems named in the route.

DERIVATION
kl-thompson-v-short-generator-words-certificate-proof
