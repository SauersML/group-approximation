---
rg: 2
id: cone-diagonal-roots-miss-a-kl-word-over-thompson-v
kind: claim
title: Internal roots after cone-diagonal endomorphisms of V cannot certify Kervaire--Laudenbach over V, already at one degree-one word with S_3 coefficients
distinct_from:
  cantor-homeomorphisms-miss-a-unimodular-root: that proves no root in Sym(Omega) for an S_3-action with orbits of sizes one and three; this identifies the census S_3 = <a,c> of V, shows that every cone-diagonal endomorphism of V keeps it of that orbit type, and so kills the retraction certificate family over V at a word where Kervaire--Laudenbach holds.
  kl-holds-over-thompson-v: that is the positive statement over V; this kills one proof method for it, and does not decide it.
  kl-thompson-v-short-generator-words-certified-injective: that uses retractions after delta_k as certificates for particular census words; this shows the same certificate family, even with the root allowed in Sym(C), is incomplete.
artifacts:
  - research/artifacts/kl-thompson-v-internal-roots-2026-09-17.md
---

**Setting.** `V` acts on the right on Cantor space `C = {0,1}^N` with the
Bleak--Quick generators `a = (00 01)`, `b = (01 10 11)`, `c = (1 00)`, as in
`experiments/kl-thompson-v-census/vgroup.py`.

**Cone-diagonal endomorphisms.** Choose `k >= 1` pairwise disjoint clopen sets
`U_1, ..., U_k` of `C` and prefix-code homeomorphisms `h_i : C -> U_i` (a
complete prefix code `p_1..p_n` mapped to a prefix code of `U_i`,
`p_j z -> q_j z`). Put `R = C \ (U_1 ∪ ... ∪ U_k)` and

    phi(g) = h_i^(-1) g h_i  on U_i,      phi(g) = id  on R.

Each `phi(g)` is in `V`, and `phi` is an injective endomorphism of `V`. The
family contains every `delta_k` over a code `P_k` (the RETRACT certificates
of the V census) and every masked endomorphism `g+1`, `g+g+1`, ... searched in
`experiments/kl-thompson-v-internal-roots-2026-09-17/rootsearch.c`.

**The word.** `w0 = c t a t a t^(-1)`, census syllable form `ctataT`, with
`deg_t(w0) = 1`.

1. **Kervaire--Laudenbach holds for `w0` over `V`.** The map
   `V -> (V * <t>)/<<w0>>` is injective.
2. **No cone-diagonal internal root.** For every cone-diagonal endomorphism
   `phi`, no `x in Sym(C)` satisfies `phi(c) x phi(a) x phi(a) x^(-1) = 1`. In
   particular there is none in `Homeo(C)`, and none in `V`.

So a root of `w0^phi` inside `V` after a cone-diagonal endomorphism never
exists, although `w0` satisfies the conjecture.

## What it kills

**The method.** Take the certificate "`V -> V_w` is injective because
`w^phi(t0) = 1` for some `t0 in V` and some cone-diagonal `phi`". This covers
the census RETRACT certificates and the 2026-09-17 internal-root search. It
cannot prove `kl-holds-over-thompson-v`: it already fails at `w0`, a
degree-one word whose coefficients generate a finite group.

**Where it dies.** Step 2 of the proof. Each `phi` keeps `phi(<a,c>)` of
orbit type `{1, 3}`, and `cantor-homeomorphisms-miss-a-unimodular-root`,
item 2, forbids a root in `Sym(Omega)` for that type.

**Why enlarging the ambient does not help.** Letting the root range over
`Homeo(C)` or `Sym(C)` keeps the obstruction, because item 2 is about
`Sym(Omega)`.

**All endomorphisms.** Every endomorphism of `V`, and every homomorphism
into `V_{n,1}`, keeps the orbit type too. This is
`higman-thompson-roots-miss-a-kl-word-over-thompson-v`, through Matte Bon's
classification, and it refutes the gate
`thompson-v-endomorphism-breaking-the-s3-orbit-type`.

**What it does not say.**
- Nothing about census frontier words. Their coefficients generate `V`, where
  no finite orbit type is available.
- Nothing about whether a violation exists.

**ESTABLISHED** through `cone-diagonal-roots-miss-a-kl-word-over-thompson-v-proof`.
- It imports `cantor-homeomorphisms-miss-a-unimodular-root`,
  `kl-failure-localizes-to-the-coefficient-subgroup` and
  `kervaire-laudenbach-holds-for-hyperlinear`.
- Otherwise it is elementary. The orbit computation of `<a,c>` is exact and
  reproduced in the artifact.
