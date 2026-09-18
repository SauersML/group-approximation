---
rg: 2
id: gl-n-q-root-is-a-coherence-problem
kind: claim
title: Coherence (MT-C) - every finitely generated subgroup of GL_n(Q) has a finitely presented simple host, GL_n(Q) embeds in an ultraproduct of such groups, and the root is equivalent to a coherent chain of embeddings
distinct_from:
  gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups: that is one assembled input, the local form; this sets it beside the finitely generated subgroups and the chain reformulation.
  ascending-unions-embed-along-coherent-chains: that is the general union criterion; this applies it to GL_n(Q) = ∪_m GL_n(Z[1/m!]).
  gl-n-q-embeds-in-fp-simple-group: that is the root; this shows which kinds of invariants cannot refute it.
artifacts:
  - research/artifacts/gq-gq-critic-2.md
---

**ESTABLISHED (assembly)** through `gl-n-q-root-is-a-coherence-problem-assembly`. The established part is the
conjunction of three landed claims, plus one direct instance of the third. No new proof is given. The heuristic
reading at the end is **not** claimed. Source: critic pass 2, `research/artifacts/gq-gq-critic-2.md` §3, MT-C.

## Established part

1. **Finitely generated pieces.** `fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups`: every
   finitely generated subgroup of `GL_n(Q)` embeds in a finitely presented simple twisted Brin–Thompson group,
   which also contains `2V` and so `Q`.
2. **Local form.** `gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups`: `GL_n(Q)` embeds in an ultraproduct
   of finitely presented simple groups. So the local form of the root holds, and no universal sentence can
   refute it.
3. **Chain form.**
   - `ascending-unions-embed-along-coherent-chains`: an ascending union embeds in a group exactly when its
     terms embed along a chain whose restrictions agree up to conjugacy.
   - Apply it to `GL_n(Q) = ∪_m GL_n(Z[1/m!])`. Every rational matrix whose inverse is rational has entries,
     and inverse entries, in some `Z[1/m!]`.
   - So `gl-n-q-embeds-in-fp-simple-group` holds for `n` iff there are a finitely presented simple `S` and
     embeddings `ι_m : GL_n(Z[1/m!]) -> S` with the restriction of `ι_(m+1)` to `GL_n(Z[1/m!])` conjugate
     in `S` to `ι_m`, for every `m`.

## Heuristic reading (not claimed)

- **The critic's reading.** No "finitary" invariant can obstruct G. That includes:
  - properties of finitely generated subgroups;
  - torsion;
  - single-element distortion;
  - FW of finitely generated pieces.
- **Where an obstruction must live.** It would have to be a growth or coherence invariant along the chain
  `u(1/m!)`, such as nucleus depth, rewrite depth, register overflow or symbol growth.
- **What is proved.** Item 1 excludes obstructions that see only finitely generated subgroups. Item 2 excludes
  obstructions expressible by a universal sentence. The broader formulation is not a theorem.
