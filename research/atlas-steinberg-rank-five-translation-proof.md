---
rg: 2
id: atlas-steinberg-rank-five-translation-proof
kind: route
title: Assemble the dictionary, the induction, and central sufficiency into the usable list
target: atlas-steinberg-rank-five-translation
requires: [atlas-steinberg-spare-index-independence, atlas-rank-five-dictionary, atlas-reverse-dictionary, atlas-relator-central-sufficiency]
---

# Assemble the dictionary, the induction, and central sufficiency into the usable list

**The list.**  `T_St` = the full (St2)/(St3) instantiation on the ring
generators (4,612 relators) + 24 involutivity relators (the 100 squares
`x_ij(a)²` minus 12 freely trivial and 64 already present in the family
— atlas-realisation coincidences, distinct from the abstract
independence) + the 12 named reverse-dictionary relators: **4,648 presentation
entries in the twelve atlas generators, every one verified to lie in `R̄` by exact
Leavitt arithmetic** (jobs 15860125, 15864167).  Step-4 acceptance passes on
the 4,636-word family-plus-involutivity probe list: 72 relators escape the
cartesian kernel (screen D) and the degree-10 screen exhausts 2·1,814,400
pairs with zero survivors.  The twelve reverse-dictionary words are verified
separately by `experiments/atlas_relator_rank5_reverse.py` and complete the
mathematical packet to 4,648.  One audit
caveat: the involutivity block alone would FAIL screen (D) — every
square projects trivially — and passes only as part of the merged list;
block-wise screening would raise a false alarm.

**Artifact provenance audit (2026-08-26).**  The historical name
`atlas-rank5-T_St.json` refers to the output of
`atlas_relator_rank5_involutivity.py --emit-merged`: it contains
`4,612 + 24 = 4,636` words and deliberately omits the reverse-dictionary
twelve.  The latter script has no JSON serializer.  No reachable Git commit
contains either that 4,636-word generated JSON or a 4,648-word fully merged
artifact.  Thus 4,648 is the proved assembly count from three reproducible
generators, while 4,636 is the count used by the warm-start and flip probes;
they are not competing counts.  The exact source chain is
`atlas_relator_rank5_full_family.py` (introduced at `0c8e3b3cf`),
`atlas_relator_rank5_involutivity.py` (`0701ceb90`), and
`atlas_relator_rank5_reverse.py` (`0c30ee812`).

`experiments/atlas_relator_rank5_complete_packet.py` now reconstructs that
assembly directly and audits a second harmless reduction effect: eight of the
twelve named reverse-dictionary relations reduce freely to the empty word.
Thus the presentation ledger has 4,648 entries, while its reduced nonempty
literal-word set has 4,640 elements.  The remaining four reverse relations are
nonempty and do not duplicate the 4,636-word probe family.  The deterministic
ordered-list checksum is
`9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99`.

**The assembly.**

1. `atlas-steinberg-spare-index-independence`: the abstract group `G₀`
   on the `X_ij(a)` with exactly these relations is isomorphic to
   `St₅(L)`.
2. The atlas quotient `G = P̄/⟨⟨T_St⟩⟩` satisfies every `G₀`-relation —
   that is what the emission verified — so there is
   `ψ : St₅(L) ≅ G₀ → G`, compatible over `Q` by construction
   (`atlas-rank-five-dictionary` sends generators to the right cosets).
3. `ψ` is surjective: `atlas-reverse-dictionary` writes the twelve atlas
   generators as `x`-words.
4. Hence `ker(G ↠ Q) = ψ(K₂(5,L))`, which is central: `K₂(5,L)` is
   central in `St₅(L)` at rank ≥ 5 — Kervaire–Steinberg, the recorded
   literature premise (Weibel III.5.5.1 pin), **the only import left on
   this route's trust surface** — and central images under surjections
   are central.
5. `⟨⟨T_St⟩⟩ ≤ R̄` since every relator is verified in `R̄`; with 4,
   `P̄/⟨⟨T_St⟩⟩` is a central extension of `Q`, so
   `atlas-relator-central-sufficiency` gives `N̄ ≤ ⟨⟨T_St⟩⟩ ≤ R̄`:
   **`T_St` is a usable relator list for the canonical regular-`A₈`
   criterion.**

**What this makes concrete.**  The §9 criterion of the atlas is now a
fully explicit finite object: `Q = L_{F₂}(1,2)^×` is hyperlinear iff
there are `k_n ≥ 1` and single unitaries `U_n ∈ U(20160·k_n)` making
the 4,648 named entries (equivalently the 4,640 reduced nonempty words) of
`T_St` — evaluated in two `U_n`-conjugate
copies of the regular representation of `A₈` — tend to `1` in
normalized Hilbert–Schmidt.  Deciding that infimum decides the
Leavitt–Steinberg fork: unstable resolves Question 3.4 negatively;
stable produces the first nonhyperlinear group.

**Trust surface, complete.**  Kervaire–Steinberg centrality (tagged
import; note only centrality is used — not universality, not
`K₂`-vanishing, not finite generation, and the once-cited
Krstić–McCool finite-presentability import is now fully discharged by
the in-repo derivation).  Everything else on this route is proved
in-repo or machine-verified exact arithmetic.
