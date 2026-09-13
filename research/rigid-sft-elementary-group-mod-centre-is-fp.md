---
rg: 2
id: rigid-sft-elementary-group-mod-centre-is-fp
kind: claim
title: Over a finitely presented free minimal SFT crossed product, some elementary group modulo its centre is finitely presented
distinct_from:
  leavitt-tensor-elementary-host-criterion: that reduces finite presentation of E_n(B ⊗ L) to finite normal generation of one unstable Steinberg kernel over Leavitt tensor rings; this is the same gate over a tracial crossed product, where no Leavitt factor and no K_1 vanishing are available.
  free-minimal-subshift-elementary-groups-are-simple-kazhdan: that proves simplicity, property (T) and linear soficity of the group modulo centre; this asks for its finite presentation once the ring is finitely presented.
---

**OPEN.** Let `Ω` be a free minimal `Z^2`-SFT such that `R = LC(Ω, F_q) ⋊ Z^2` is finitely
presented. Then for some `n >= 4` the group `EL_n(R)/Z(EL_n(R))` is finitely presented.

This is gate (b) of `sofic-fp-simple-kazhdan-group-from-fp-simple-ring` and of
`fp-simple-kazhdan-linear-sofic-group-exists`. For `n >= 4`, simplicity of `EL_n(R)` modulo centre
follows from the `n = 3` box-tower argument, transcribed with more indices.

## Attempts

- **Reduction.**
  - Krstić--McCool (JPAA 141 (1999), Theorem 3, quoted in
    `research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md`) makes `St_n(R)`
    finitely presented for `n >= 4`.
  - `S_n` is simple and `St_n(R)` is perfect, so `S_n` is finitely presented iff the kernel of
    `St_n(R) -> S_n` is finitely normally generated.
  - When the unstable Steinberg kernel `K_2(n, R)` is central, this is finite generation of
    `K_2(n, R)`, up to the finite scalar part.
- **Heuristic K-theory (not verified).**
  - `LC(Ω, F_q)` is a filtered colimit of finite products of `F_q`, hence regular.
  - Iterating the twisted Bass--Heller--Swan sequence would give `K_2(R)` built from
    `H_2(Z^2; K_0) = Z` (the symbol `{u_1, u_2}`) and `H_1(Z^2; LC(Ω, F_q^x))`.
  - The latter is finitely generated when the tiling cohomology of `Ω` is, as for self-similar
    tilings.
  - Unchecked: K-regularity of the intermediate crossed product, the stable rank of `R`, unstable
    surjective and injective stability, and centrality of `K_2(n, R)`.
- **Contrast.** For the Leavitt hosts the analogous gate is `K_2`-regularity of `B ⊗ L`. Here the
  symbol `{u_1, u_2}` of the two commuting translations is a genuine infinite-order class, but it is
  finitely generated.
