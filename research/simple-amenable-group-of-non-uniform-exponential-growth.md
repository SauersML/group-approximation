---
rg: 2
id: simple-amenable-group-of-non-uniform-exponential-growth
kind: claim
title: There is an infinite finitely generated simple amenable group of non-uniform exponential growth
distinct_from:
  simple-kazhdan-lef-group-of-non-uniform-exponential-growth: that example is Kazhdan, hence far from amenable; this example is amenable, the derived topological full group of the Thue–Morse subshift.
---

**ESTABLISHED (unreviewed; sk-cornulier-q7).** The example is `[[T]]′` for the Thue–Morse subshift.

**Context.**
- Gromov (1981) asked whether exponential growth forces uniform exponential growth; Wilson (2004) answered no, with residually finite branch groups.
- Kourovka 21.117(a) asks for a finitely generated simple example. Sauer–Schesler (arXiv:2605.30163) answered it with Thompson's `V`, which is not amenable.
- Osin (2003) showed that elementary amenable groups of exponential growth have uniform exponential growth. So an amenable simple example must be non-elementary amenable, and `[[T]]′` is.

**Novelty (bounded).** Three web searches and a grep of main found no amenable simple example and no growth-rate result for derived full groups.

Route: `simple-amenable-non-uniform-growth-from-thue-morse`.

**Review (sk-verify-16, 2026-09-13): PASS**, conditional on `dyadic-substitution-derived-full-groups-non-uniform-growth` (PASS, same review) and the Matui and Juschenko–Monod imports. Thue–Morse satisfies the hypotheses, and the example is simple, f.g., amenable and infinite. See `research/artifacts/sk-verify-16-2026-09-13-part3.md` §3.

**Review (sk-verify-17, 2026-09-13): PASS**, independent of sk-verify-16. For Thue–Morse the tower partition needs no Mossé import, and [[T]]′ is infinite, f.g., simple (Matui), amenable (Juschenko–Monod), of exponential growth (Cornulier Théorème `expo`, l.781–784), with ω = 1. Novelty wording: keep "not found in a bounded search". The bound was 4 web searches, the Kourovka 21.117 printed answer (V only), and greps of both Sauer–Schesler e-prints (the only amenable reference is Osin). Brieussel's amenable non-uniform examples are not simple. See `research/artifacts/sk-verify-17-2026-09-13.md` §§4–5.
