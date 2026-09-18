---
rg: 2
id: shell-envelopes-depend-only-on-the-near-image
kind: claim
title: A genuine-action shell envelope depends only on the near image of the input, so every finitely generated group of index-zero near permutations has a shell envelope and realizability is never an obstruction
distinct_from:
  genuine-action-shell-envelopes-generalize-the-regular-shell: that builds the shell from a genuine action; this shows the envelope sees only the near classes, so any finitely generated subgroup of index-zero near permutations defines one, via arbitrary lifts.
  shell-cantor-embeddings-are-finite-germ-extensions: that is the regular construction; the observation here is about which data the envelope depends on.
artifacts:
  - research/artifacts/gq-bh-shell-universal-genuine-actions.md
---

**ESTABLISHED** (lane proof below; elementary; not independently reviewed; no novelty claimed).

**Setting.** `NearSym(N) = Sym*(N)/FSym(N)`; `NearSym_0(N)` is the index-zero part, i.e. the image of
`Sym(N)`. For `P <= Sym(N)` let `E_P = <V, hat(P)>` be the shell envelope of
`genuine-action-shell-envelopes-generalize-the-regular-shell` (transfer to the even cones, odd cones fixed).

1. If `P, P' <= Sym(N)` satisfy `P·FSym(N) = P'·FSym(N)`, then `E_P = E_(P')`.
2. For every finitely generated `Gamma <= NearSym_0(N)`, choose lifts of a finite generating set and let
   `P_Gamma <= Sym(N)` be the group they generate. Then `E_Gamma := E_(P_Gamma)` does not depend on the
   choice of lifts. It contains `hat(tilde Gamma)` for the full preimage `tilde Gamma <= Sym(N)` of `Gamma`,
   hence every group acting genuinely and faithfully on `N` with near image inside `Gamma`.
3. The isotropy germ group of `E_Gamma` at `p` is `<Gamma^even, tau>`, and the near group is
   `R_Gamma = <Gamma, s>`. The germ gates, the finitely generated point stabilizers, and the
   twisted Brin–Thompson step of the generalization claim apply verbatim.

**Proof.** A finitary permutation `f` of `N` gives a `hat(f)` that permutes finitely many cones
`0^(2n) 1 C` by prefix replacement and is the identity on the rest of `C`, including a neighbourhood
of `p`. So `hat(f) ∈ V`. If `pi' = pi f`, then `hat(pi') = hat(pi) hat(f) ∈ <V, hat(pi)>`. So
`E_P = E_(P·FSym) = E_(P')`, which is (1). (2) follows because any two lift choices differ by finitary
permutations, and `tilde Gamma = P_Gamma·FSym(N)`. The germs of `hat(pi)` at `p` see only the near class
of `pi`, which gives (3). The finite generation of `S(M,F)` uses only a finite generating set of `P_Gamma`.

**Consequence.** The realizability clause of `fp-ray-near-actions-with-the-shift-exist` is unnecessary.
The shell programme is a statement about finitely generated subgroups of `NearSym_0(N)`, and the
input that embeds is any genuine lift group. The infinite-support hypothesis is also unnecessary for
the embedding: finitary elements of a lift group land in `V`, and the group still embeds.
