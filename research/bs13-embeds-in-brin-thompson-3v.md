---
rg: 2
id: bs13-embeds-in-brin-thompson-3v
kind: claim
title: The Baumslag-Solitar group BS(1,3) embeds in the Brin-Thompson group 3V
distinct_from:
  bs12-embeds-in-brin-thompson-2v: that asks for BS(1,2) (an element conjugate to its square) in some nV; this is BS(1,3) in 3V.
  bs-1-n-does-not-embed-in-thompson-v: that excludes every BS(1,n), n >= 2, from V; this puts BS(1,3) in 3V.
  renormalizable-thompson-elements-give-baumslag-solitar: that is the general criterion; this is its first instance.
---

**ESTABLISHED (2026-09-18)** through `bs13-in-3v-via-smart-renormalization`, both inputs reviewed PASS
(gq-referee-a 12b5beb4a, gq-referee-b b6d33ae8e). There are `s, u ∈ 3V` with `s` of infinite order and `u s u^-1 = s^3`, so
`BS(1,3) = ⟨a, t | t a t^-1 = a^3⟩ ≅ ⟨s, u⟩ ≤ 3V`.

**Credit and scope.**
- The priority check (gq-lit-arxiv, e78b09c00, bounded search, no MathSciNet) found no earlier `BS(1,n)`,
  `|n| >= 2`, in any Brin–Thompson group `nV` or reversible-Turing-machine group. The statement is about
  the untwisted groups `nV`: Bux–Llosa Isenrich–Wu (arXiv:2408.05673) already place every Baumslag–Solitar
  group in a twisted Brin–Thompson group `SV_G`, through a type (A) action.
- The element comes from the SMART machine of Cassaigne–Ollinger–Torres-Avilés, via Callard–Salo's
  analysis (arXiv:2208.00685v3). Their Theorem E gives distortion `O(log^4 N)` in `mV`; this gives
  `|s^{3^n}| = O(n)` in `3V`.
- It does not answer Callard–Salo's question for `Aut(A^Z)` ("It is not known whether the Heisenberg
  group or the Baumslag-Solitar group BS(1,2) embed in Aut(A^ℤ)"). It does not answer Salo's `Aut_2`
  question either, nor anything about `BS(1,2)`.

**What it gives.**
- An element of `3V` with logarithmic distortion, `|s^{3^n}| = O(n)`. Callard–Salo's distortion element
  of `mV` (a different construction) has `|f^N| = O(log^4 N)`.
- As far as the bounded priority search shows (gq-lit-arxiv, e78b09c00), it is the first `BS(1,n)` with
  `|n| >= 2` in a Brin–Thompson group `nV`. `BS(m,±m)` already lies in `V`.
- The Baumslag–Solitar gate of `rational-stepping-stones-in-nv-need-bs12-or-heisenberg` is passed
  for the prime 3. The gate for 2, which `GL_2(Q)` and `Aff(Q)` need, stays open.
- It is consistent with the withdrawal of Sheng arXiv:2209.11982 (v2, "a flaw in one of the proofs"),
  whose abstract excluded some Baumslag–Solitar groups from `SV` and `SV_G`.
