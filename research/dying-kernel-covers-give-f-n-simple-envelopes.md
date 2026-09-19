---
rg: 2
id: dying-kernel-covers-give-f-n-simple-envelopes
kind: claim
title: If a contracting self-similar group has a type F_n wreath-recursion cover with dying kernel, then it embeds in a simple group of type F_n; in particular every iterated monodromy group of a hyperbolic post-critically finite rational map embeds in a simple group of type F_infinity
distinct_from:
  wreath-recursion-thompson-groups-inherit-fn: that gives type F_n for the Röver–Nekrashevych groups V_{d,r}(G); this adds the simple envelope SV_{V_d(G)} through Belk–Zaremsky and the stabilizer reduction.
  fp-self-similar-groups-embed-in-fp-simple-groups: that gives finitely presented simple envelopes for finitely presented self-similar groups; this gives type F_n simple envelopes for groups with F_n dying-kernel covers, which are typically infinitely presented.
  twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family: that is the conditional reduction for all full contracting RSGs; this discharges its hypothesis for Röver–Nekrashevych groups whose self-similar group has a good cover.
---

**ESTABLISHED** (lane proof `bh-free-06`, 2026-09-18; a composition of established lane nodes; not
independently reviewed). The composition was suggested by `bh-free-45`. No priority claimed.

## Statement

Let `G ≤ Aut(T_d)` be finitely generated, contracting and self-similar. Suppose `G` has a wreath
recursion cover `B` of type `F_n` with dying kernel. Then:
- `SV_{V_d(G)}` is a simple group of type `F_n` that contains `V_d(G)`, and hence `G`;
- for `n = ∞` it has type `F_∞`.

**Corollary.** For every hyperbolic post-critically finite rational map `f`, `IMG(f) ≤ V_f ≤
SV_{V_f}`, and `SV_{V_f}` is a simple group of type `F_∞`.

## Proof

1. **The finiteness family.** `V_d(G)` is a full contracting RSG over the full shift. This is
   implicit in BBMZ arXiv:2309.06224, TeX l.221–222, which calls Röver–Nekrashevych groups of
   contracting groups a special case of `quest:F_infty`.
   - Its family `𝓕` of full RSGs with the same nucleus on clopen `E' ⊆ E` consists of the full
     groups on `E' ≅ [r] × X^ω`.
   - A homeomorphism of `E'` whose deep local similarities lie in the nucleus `N` is exactly an
     element of `V_{d,r}(⟨N⟩) = V_{d,r}(G)`. So `𝓕 = {V_{d,r}(G) : r >= 1}`, up to isomorphism.
2. **Every member of the family has type `F_n`**, by `wreath-recursion-thompson-groups-inherit-fn`.
3. **The simple envelope.** By `twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family`
   items 1–2, which combine Belk–Zaremsky Thm 4 with stabilizers that are iterated ascending HNN
   extensions over members of `𝓕`, `SV_{V_d(G)}` has type `F_n`. It is simple, as that node uses.
4. **The corollary** follows from `hyperbolic-pcf-rational-nekrashevych-groups-are-f-infinity`,
   whose cover `π_1(M)` is free. `∎`

**Distortion.** `V_d(G)` is undistorted in `SV_{V_d(G)}`
(`hyperbolic-groups-undistortedly-embed-in-fp-simple-groups`, for full contracting RSGs). But `G`
itself is typically **distorted** in `V_d(G)`.
- Contraction writes `g` as a tree pair of depth about `log_{1/λ}|g|` with nucleus labels, so
  `|g|_{V_d(G)} = O(|g|^{log d / log(1/λ)})`.
- This is sublinear when the contraction ratio satisfies `λ > 1/d`.
- So no quasi-isometric claim is made for `G`.

## Lesson for general BH

**For full-group hosts, the whole "simple envelope of type F_n" problem is one question: find an
F_n group covering the nucleus data whose kernel dies under splitting.**
- The stabilizer and orbit clauses of Belk–Zaremsky cost nothing, by bh-free-45's reduction.
- Faithfulness of the labels costs nothing, by `wreath-recursion-thompson-groups-inherit-fn`.
- For hyperbolic groups, the one remaining gate is such a cover for the horofunction RSG
  `[[G*Z | ∂_h]]` (gate (a)). If it holds, every hyperbolic group, Kazhdan ones included, lies in an
  F_∞ simple group.
