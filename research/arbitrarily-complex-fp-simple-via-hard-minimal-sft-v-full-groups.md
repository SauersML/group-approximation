---
rg: 2
id: arbitrarily-complex-fp-simple-via-hard-minimal-sft-v-full-groups
kind: route
title: Take a minimal free Z^2-SFT with a language beyond the bound and the alternating full group of V times its transformation groupoid; its word problem inherits the language
target: fp-simple-groups-with-arbitrarily-complex-word-problem
requires:
  - v-times-minimal-free-sft-alternating-full-groups-are-fp
  - minimal-free-z2-sfts-have-arbitrarily-hard-row-languages
  - alternating-v-full-group-wp-computes-sft-language
  - nekrashevych-symmetric-and-alternating-full-groups
  - v-times-ample-full-groups-are-generated-by-transpositions
---

**Route.** The implication below is complete. Two of its three substantive
premises are ESTABLISHED in this wave. The only OPEN premise is (P2), and it is
needed only for `Λ = Z^2` and the specific hard SFTs of the second premise.

**How this differs from nearby routes.**
- `complex-fp-simple-groups-from-boone-higman` needs the full conjecture; this
  needs only a finiteness statement with no input group.
- `arbitrarily-complex-fp-simple-via-hard-type-a-actors` needs hard actors with
  finitely generated stabilizers and finitely many orbits on pairs, and hardness
  must be built into the actor's word problem. Here hardness is supplied
  unconditionally by the subshift, and no premise mentions complexity except the
  established ones.
- `boone-higman-via-v-times-aperiodic-sft-full-groups` uses (P2) together with
  the embedding premise (P1). This route shows that (P2) **alone** already
  forces finitely presented simple groups beyond every recursive bound. So (P2)
  cannot be proved by any argument that also bounds the word problem of the
  resulting presentations uniformly over the minimal free `Z^2`-SFTs.

## Proof

Fix recursive `R`. Assume `R` is non-decreasing with `R(n) >= n`, as in the
premise proofs. Put `R_4(n) = R(n^4)`, which is recursive, non-decreasing and
at least `n`.

1. By `minimal-free-z2-sfts-have-arbitrarily-hard-row-languages` applied to
   `R_4`, choose a nonempty minimal free SFT `X ⊆ Σ^(Z^2)` with
   `L_row(X) ∉ F(R_4)`.
2. Put `T = G_V × (Z^2 ⋉ X)`. By (P2)
   (`v-times-minimal-free-sft-alternating-full-groups-are-fp`, with `Λ = Z^2`,
   which is infinite and finitely presented), `A(T)` is finitely presented.
3. `A(T)` is simple and nontrivial. By steps 1--4 and 7 of
   `boone-higman-via-v-times-aperiodic-sft-full-groups`, `T` is an effective
   minimal ample Hausdorff groupoid on the Cantor space `C × X`. Those steps use
   only that `X` is nonempty, minimal and free, and that `Λ` is infinite.
   Nekrashevych's Theorem 4.1, quoted in
   `nekrashevych-symmetric-and-alternating-full-groups`, then gives simplicity.
   `A(T) = F(T)` contains `Z^2` by
   `v-times-ample-full-groups-are-generated-by-transpositions`.
4. `A(T)` contains the subgroup `Q` of
   `alternating-v-full-group-wp-computes-sft-language` (clause 1) and is
   finitely generated. If its word problem were in `F(R)`, clause 3 would put
   `L_row(X)` in `F(R_4)`, contradicting step 1.

So `A(T)` is a finitely presented simple group whose word problem is not in
`F(R)`. `∎`

## Where it can fail

- **(P2) for hard SFTs.** This is the whole remaining content. A live lemma
  this wave (swarm-0917-w6-w6-bh-break, necessary condition on
  finitely presented V-full groups over free subshifts: connected difference
  sets, no finite asymptotic pairs) constrains the SFTs that (P2) can hold for.
  Whether the Durand--Romashchenko SFTs used in step 1 meet that condition is
  unchecked. The route is no evidence against (P2): its conclusion is also a
  consequence of `boone-higman-conjecture` and is expected to be true.
- **Narrowest sufficient form.** It is enough that, for every recursive `R`,
  **some** minimal free `Z^2`-SFT with `L_row(X) ∉ F(R_4)` has finitely presented
  `A(G_V × (Z^2 ⋉ X))`. The premises do not need this for all minimal free SFTs.
