---
rg: 2
id: labbe-shift-derived-full-group-is-finitely-presented
kind: claim
title: The derived subgroup of the topological full group of Labbé's minimal aperiodic Wang shift is finitely presented
distinct_from:
  periodic-approximable-subshifts-host-no-fp-simple-group: That kills finitely presented simple subgroups for subshifts with periodic approximations, including minimal Z-subshifts; this asks for finite presentation over Labbé's aperiodic Z^2 SFT, where that obstruction provably cannot fire.
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

**OPEN.** Let `Omega_U` be Labbé's 19-tile Wang shift (`minimal-aperiodic-wang-shift-exists`). The group `D([[Z^2 ~ Omega_U]])` is finitely presented.

**Why it matters (2026-09-12, ex-fp-simple-sofic).** This one claim now carries
`hyperlinear-fp-infinite-simple-group` by itself, through
`fp-simple-amenable-orbit-via-labbe-shift` and
`hyperlinear-fp-simple-via-amenable-orbit-full-group`. The group is sofic
unconditionally (`amenable-orbit-full-group-subgroups-are-sofic`), so a proof of
finite presentation gives a finitely presented infinite simple sofic group with no
amenability input. It would also serve `fp-infinite-simple-amenable-group`, but
only together with `labbe-shift-derived-full-group-is-amenable`.

## Attempts

- **Refutation through SFT neighbourhoods (the suggested mechanism "finite presentation forces periodic points").** Dead as it stands.
  - `fp-subshift-full-group-subgroups-extend-to-sft` produces an SFT neighbourhood, and `Omega_U` is already one.
  - Any argument that reads only finite orbits of SFT neighbourhoods is blind here, by `sfts-without-finite-orbits-are-not-residually-finite-actions`.
  - That also rules out Ma's LEF theorem and Grigorchuk--Medynets-style LEF arguments as stated.
- **Positive results.** None apply.
  - Matui's finite presentation (arXiv:1210.5800) covers one-sided irreducible SFT groupoids, which are compressible and so non-amenable (`amenable-full-group-forces-invariant-measure`).
  - Nekrashevych's finitely presented groups (arXiv:1312.5654, lines 50–90) come from expanding maps and hyperbolic groupoids.
  - Neither covers two-dimensional SFT groupoids, and the sources read contain no finite presentation criterion for `Z^2`-SFT full groups.
- **Isolation.** No contradiction found. A finitely presented infinite simple group is isolated in the space of marked groups. `D([[Omega_U]])` is sofic by the Elek--Szabó remark in Elek--Monod line 128, and soficity gives no contradiction with isolation.
  - Non-isolation would need marked groups converging to `D([[Omega_U]])` and different from it.
  - None of them is the rule group of a validly coloured `Z^2`-set (`minimal-free-sft-full-group-pattern-models-are-exact`). So any refuting approximants must show forbidden patterns, or not be spatial at all.
- **Grigorchuk--Medynets (arXiv:1105.0719, read from source).**
  - Mechanism: Theorem 5.1 makes `[[T]]` LEF for minimal `Z`-subshifts. It factors each element uniquely as `Q = S_Q R_Q`, a permutation of atoms inside Kakutani--Rokhlin towers times a rotation. Line 174: finitely presented and LEF imply residually finite. Line 176: so `[[T]]'` is infinitely presented.
  - Failure point: Kakutani--Rokhlin towers are finite periodic models. `Omega_U` has no finite validly coloured model (`sfts-without-finite-orbits-are-not-residually-finite-actions`), and every infinite one gives the group back exactly.
  - Still open: whether `D([[Omega_U]])` is LEF. A proof of LEF would refute this claim, since an infinite simple group is not residually finite.
- **Matui, "never finitely presented" (math/0404117, theorem following line 1104, read from source).**
  - Mechanism, in five steps:
    1. Recode the minimal subshift `X` inside an SFT `Y` on which one set of cylinder rules generates `D([[Z]])` for every minimal `Z ⊆ Y`.
    2. The finitely many relators hold on a clopen set whose invariant core `Y_1 ⊇ X` is an SFT.
    3. Every minimal `Z ⊆ Y_1` has `D([[Z]])` a quotient of `D([[X]])`. Simplicity makes the two isomorphic, and `Z` is then flip conjugate to `X`.
    4. The embedding lemma (line 1070) supplies non-conjugate `Z ⊆ Y_1`. It says a minimal subshift embeds into an irreducible SFT of period `p` iff its entropy is smaller and `[1_X]` is divisible by `p` in `K^0`, via Lind--Marcus Corollary 10.1.9.
    5. That is a contradiction.
  - Failure points for `Z^2`; there are three, each independent of the others.
    - (a) `Y_1 ⊋ X` holds only because an infinite minimal `Z`-subshift is never an SFT. `Omega_U` is an SFT, so nothing forces `Y_1 ≠ Omega_U`, and any other minimal `Z ⊆ Y_1` shows forbidden patterns (`minimal-free-sft-full-group-pattern-models-are-exact`).
    - (b) The embedding lemma is one-dimensional, and no source read gives a `Z^2` analogue for SFTs containing `Omega_U`.
    - (c) The rigidity input is weaker. For minimal essentially principal groupoids, isomorphic derived full groups only give isomorphic groupoids (Matui arXiv:1210.5800, Theorem `iso`, line 888). That is continuous orbit equivalence, not flip conjugacy, so `Z` would have to be not continuously orbit equivalent to `Omega_U`.
- **Matui, finite presentation for one-sided SFTs (arXiv:1210.5800, Theorem `finite`, line 3245, read from source).**
  - Mechanism: type `F_∞` via Brown's criterion (line 2706) on a complex of cylinder-set expansions (lines 2708--2834).
  - Failure point: expansions ride on the shift's local homeomorphisms, i.e. compression. `Omega_U`'s full-support invariant measure forbids compression (`labbe-shift-derived-full-group-escapes-known-obstructions`, item 2), so a non-compressing replacement is needed.
- **Presentations for minimal subshifts (arXiv:1508.04454, Theorem `IntroMain`, lines 70--96, read from source).**
  - It gives an infinite presentation, with generators indexed by words of the language, and a solvable word problem iff the language is recursive.
  - It gives no finite presentation and no finiteness criterion.
- **Li, products of one-sided SFTs (arXiv:2110.04505, abstract only).** Proves type `F_∞` for topological full groups from products of shifts of finite type, through Garside categories of bisections. Those groupoids are compressible, so the method does not reach an invariant-measure groupoid such as `Z^2 ~ Omega_U`.
- **Not verified from source:**
  - Brin's `2V` method;
  - the Bieri--Geoghegan--Kochloffel `Σ`-invariants;
  - Matte Bon's work.
  - The Kerr--Nowak input seen, via Ma arXiv:2209.00580 near line 1287, concerns residual finiteness only.
