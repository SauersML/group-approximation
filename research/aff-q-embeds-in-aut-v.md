---
rg: 2
id: aff-q-embeds-in-aut-v
kind: claim
title: The affine group Aff(Q) embeds in the automorphism group of Thompson's group V
distinct_from:
  pgl-2-q-embeds-in-the-rational-group: that puts PGL_2(Q), hence Aff(Q), in the rational group R through a copy that does not normalize V; this asks for a copy inside Aut(V) = N_{Homeo(C)}(V), the bi-synchronizing part of R.
  aff-q-does-not-embed-in-aut-thompson-f: that excludes Aff(Q) from Aut(F); this is the same question for V, where V is not residually finite and the automorphism group is much larger.
  fg-automorphism-hosts-contain-no-divisible-subgroup: that excludes (Q,+) from Aut(Γ) for finitely generated residually finite Γ; V is not residually finite, so it does not apply here.
  aff-q-embeds-in-fp-simple-group: that is the stepping stone with a finitely presented simple host; Aut(V) is not simple, and a copy here would first need a finitely presented subgroup of Aut(V) containing it.
---

**OPEN.** Is there an injective homomorphism `Aff(Q) = Q ⋊ Q^x → Aut(V)`?

**Why it was asked.** Lane gq-critic, pass 2, rank 5: `Aut(V)` is the cheapest test of the
rational-similarity route for `n = 2`. By Rubin's theorem `Aut(V)` is the normalizer of `V`
in `Homeo({0,1}^N)`. Bleak–Cameron–Maissel–Navas–Olukoya describe it inside the rational group
`R` as the elements given by bi-synchronizing transducers, with `Out(V) ≅ O_2` (not re-read
at the source here).

**Established facts** (lane gq-deep-free-3, hand proofs, not independently reviewed):
1. **Reduction to Out(V).** Every nontrivial normal subgroup `N` of `Aff(Q)` contains the
   translations `Q`. If `N` contains `t_b: x ↦ x + b` with `b ≠ 0`, conjugating by the
   dilations gives every `t_{ab}`. If `N` contains `g: x ↦ ax + b` with `a ≠ 1`, then
   `g t_c g^-1 t_c^-1 = t_{(a-1)c} ∈ N`. By Higman (survey arXiv:2306.16356v3, Theorem 4.4)
   `V` contains no copy of `(Q,+)`, so any `Aff(Q) ≤ Aut(V)` meets `V` trivially and maps
   injectively to `Out(V)`. A positive answer therefore needs `Aff(Q) ≤ Out(V) ≅ O_2`.
2. **The rational copy fails.** The copy in `pgl-2-q-embeds-in-the-rational-group` does not
   normalize `V` (item 5 there). So `Aff(Q) ≤ R` gives nothing here directly.

## Attempts
- 2026-09-18 (gq-deep-free-3): the reduction and the failed natural copy above. Next test: do
  bi-synchronizing transducers admit infinitely divisible elements (roots of every order of
  one element of `O_2`)? A "no" kills this claim through fact 1, since `Q ⊂ Aff(Q)` would have
  to embed in `O_2`.
