---
rg: 2
id: harmonic-cuntz-simple-group-is-finitely-presented
kind: claim
title: The harmonic Cuntz simple group EL_3(C_h)/Q^x is finitely presented
distinct_from:
  harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q: that proves the group finitely generated, simple and containing every GL_n(Q); this asks for a finite presentation.
  rational-leavitt-simple-group-embeds-in-fp-simple-group: that asks for some finitely presented simple overgroup of L_Q(1,2)^x/Q^x; this names one candidate, which contains that group.
  finitely-presented-harmonic-cuntz-ring-contains-q: that is finite presentation of a ring mapping onto C_h; this is finite presentation of the simple group.
refuted_by:
  - harmonic-cuntz-simple-group-is-not-finitely-presented
artifacts:
  - research/artifacts/gq-gq-cuntz-cstar-dictionary.md
---

**OPEN.** The group `Λ_h = EL_3(C_h) / (Q^x · I)` of
`harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q` is finitely presented.

With that claim this gives `gl-n-q-embeds-in-fp-simple-group` for every `n` at
once (route `gl-n-q-via-harmonic-cuntz-host`), and
`rational-leavitt-simple-group-embeds-in-fp-simple-group` (route
`rational-leavitt-fp-simple-via-harmonic-host`).

## What is known about the question

- **Not through EL_3 itself.** `Q^x · I` is central and not finitely generated. So
  if `EL_3(C_h)` were finitely presented, `Λ_h` would not be (B. H. Neumann; part 6
  of the claim above). A presentation must impose the scalar relations
  `λI = 1` for every `λ ∈ Q^x` through finitely many relators.
- **A finitely presented ring upstairs.** `finitely-presented-harmonic-cuntz-ring-contains-q`
  gives a six-generator finitely presented ring `R_Q ->> C_h`. Whether this map is
  injective is not known. If it is, `C_h` is itself a finitely presented ring.
- **K_2 of Q does not obstruct stably.** `K_2(Q) = Z/2 ⊕ ⊕_p F_p^x` is not finitely
  generated. Its image in `K_2(C_h)` is `0`, because the map factors through
  `K_2(L_Q(1,2)) = 0`: Ara–Brustenga–Cortiñas, Theorem 7.6, in
  `abc-leavitt-path-k-theory-exact-sequence`, where the map `1 - N^t` is
  multiplication by `-1`. So in the stable Steinberg group, the Steinberg symbols of
  `Q` impose no relation beyond the Leavitt structure. The unstable `St_3` case is
  not settled.

## Attempts

- **Steinberg presentation (open).** `St_3(R)` has finitely many generators
  `x_ij(s)` for a finitely generated ring `R`. Two questions remain for
  `R = R_Q`:
  - whether finitely many Steinberg relations, together with the ring relators of
    `R_Q`, imply all the others;
  - how the kernel `St_3(R_Q) -> Λ_h` (unstable `K_2`, the kernel of
    `R_Q -> C_h`, and the scalars) is normally generated.

  Neither is done. Shared with `gq-en-ring`, `gq-k2-q` and `gq-malcev-ring`.
- **Refuted (lane `gq-malcev-ring`, 2026-09-17).** The claim is false:
  `harmonic-cuntz-simple-group-is-not-finitely-presented`. `EL_3(C_h)` is perfect, and
  its centre `Q^x·I` is not finitely generated. By the five-term sequence, a finitely
  presented central quotient would make that centre a quotient of the finitely
  generated `H_2(Λ_h; Z)` (group lemma, part 0 of
  `leavitt-scalar-commutators-block-fp-central-quotients`). So the Neumann remark
  above is not symmetric: `Λ_h` is never finitely presented, whatever `EL_3(C_h)`
  is.
