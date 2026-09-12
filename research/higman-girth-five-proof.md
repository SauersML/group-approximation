---
rg: 2
id: higman-girth-five-proof
kind: route
title: Baumslag--Solitar coordinates and amalgam normal forms exclude every short relation in Higman's group
target: higman-group-has-girth-five-in-its-standard-generators
requires:
  - higman-group-splits-as-amalgams-over-free-subgroups
artifacts:
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

## Why sufficient

Artifact Section 5.
* **Lemma 5.1.** In `BS(1,2) = Z[1/2] x| Z` a short trivial word has stable-letter exponent sum 0, so it is
  `x^(-1) y^k x y^l = y^(2k+l)` or `x y^k x^(-1) y^l = y^(k/2+l)` up to cyclic permutation. Vanishing needs
  `|k| + |l| >= 3`.
* **Theorem 5.2, one splitting factor.** A word avoiding `d` lies in `G_1 = B(a,b) *_<b> B(b,c)`. The only short
  syllables in the amalgamated `<b>` are `a^(-1) b^(+-1) a`, and what remains is a single letter.
* **Theorem 5.2, both factors.** A word containing `b` and `d` factors into syllables of length at most 3 in
  `G_1 = <a,b,c>` and `G_2 = <c,d,a>`. The only ones in `F = <a,c>` are `b^(-1) c^(+-1) b` and `d^(-1) a^(+-1) d`, which
  leave one letter outside `F`. Otherwise the normal form theorem for `H = G_1 *_F G_2` applies.
* **The Sidon consequence.** A coincidence of quotients of `{1,a,b,c,d}` is a trivial word of length at most 4.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently.
- **Lemma 5.1.** Only `(|k|,|l|)` in `{(1,0),(2,0),(1,1)}` are possible, and none vanish.
- **Both splitting cases.** The `<b>`-syllables are `a^-1 b^(+-1) a`, and the `F`-syllables are `b^-1 c^(+-1) b` and `d^-1 a^(+-1) d`. The two-letter syllables and `b c b^-1` lie outside, and `d` is not in `F`.
- **Sidon step.** `m^-1 m'` with `m != m'` in `{1,a,b,c,d}` are distinct reduced words.

Wording note on the claim node: its "form a counterexample takes" parenthetical cites an OPEN node and overstates. The filter excludes only binary unbalanced designs
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 26).
