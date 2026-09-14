# Lane ms-intro-2 (SK note): "LEF groups", part (iv) of the proof of cor:lef

Target: the note at tip c8b6021ca (22:49, 771 lines, md5 9144d853…). Brief: ct/ROSTER-sk.md, "LEF LANES 21:22".
Rows are keyed by the 12-hex sentence hash of `metadata/SK_SENTENCE_CENSUS.tsv`, but the census is still at 9047d0d3c.
The hashes below are the 9047d0d3c ones. The sentences were rewritten at c8b6021ca, so they get new rows when skf-census
regenerates.

CLAIM part (iv) (21:3x; re-checked at the tip 23:1x), in the new module
`GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFDiagonalCommutators.lean`.

At c8b6021ca the text survives, reworded (tex 395–402): "Finally, `ξ ↦ diag(u_ξ,1,1)` is an injective homomorphism
`Λ → GL_3(R_Δ)`. It maps `[Λ,Λ]` into `G_Δ`, since over `F_2` every unit `v` satisfies `diag(v,v^{-1},1) =
e_12(v)e_21(v^{-1})e_12(v) e_12(1)e_21(1)e_12(1)`, and the product of these matrices for `v = c`, `c'` and `(c'c)^{-1}` is
`diag(cc'c^{-1}c'^{-1},1,1)`. So `G_Δ` contains `Γ ≤ [Δ,Δ] ≤ [Λ,Λ]`." Tex 412–417 use the same identities for
`g ↦ diag(w_g,1,1)`, which embeds the derived subgroup of the topological full group in `G_X`.

Carriers, all over a unital ring `R` with `u : Λ →* Rˣ`:
- `PrintedLEFDiagonalIdentities`, `printedLEFDiagonalIdentities`: the first identity under `2 = 0` and the product
  identity. `whitehead_charTwo_needed`: the first identity fails over `ℤ`.
- `PrintedLEFDiagonalEmbedding`, `printedLEFDiagonalEmbedding`: `lefDiagonalHom u` is injective, equals `diag(u_ξ,1,1)`,
  maps `[Λ,Λ]` into `elementaryGroup (Fin 3) R`, and every `Γ ≤ [Δ,Δ]` lies in `[Λ,Λ]` and maps into `EL_3(R)`.
- Consumes `Leavitt/ElementaryGroup` and `KOne/BlockWhitehead` (`diagAtHom`, `diagPairAt_mul`,
  `diagAt_commutatorElement_mem`).
- For tex 412–417, apply the same theorem with `Λ` the topological full group and `u = w`.
- Signed counterpart, already on main: `Leavitt/DiagonalElementary` has `w u = e_12(u)e_21(-u^{-1})e_12(u)`,
  `balanced u = w u · w(-1) = diag(u,u^{-1},1)` and `firstDiagonalUnit_commutator`, the same product for `a`, `b`,
  `(ba)^{-1}`. The printed char-2 form with `e_21(v^{-1})` and `e_12(1)e_21(1)e_12(1)` is not there, and neither are the
  embedding of `Λ` and `Γ ≤ [Δ,Δ] ≤ [Λ,Λ]`.

| hash (9047d0d3c) | tex at c8b6021ca | sentence | status | carrier |
|---|---|---|---|---|
| 58f4e8dc5ed5 | 395–396 | the embedding `ξ ↦ diag(u_ξ,1,1)` (was "ℓ ↦ u_ℓ embeds L in GL_1(R)") | formalized | `lefDiagonalHom_injective`, `lefDiagonalHom_val` |
| 36fec8cc638b | 396–401 | the two identities | formalized | `printedLEFDiagonalIdentities` |
| 17c59a49b0ee | 396–402 | `[Λ,Λ]` into `G_Δ`, and `Γ ≤ [Δ,Δ] ≤ [Λ,Λ]` | formalized | `printedLEFDiagonalEmbedding` |

**LANDED a39853967** (23:5x): probe 0913-234246-2153 GREEN, `#audit_closed_axioms` on both endpoints, no sorryAx, and
wire-queued.

Census rows (09-14 09:3x). The census is at 696c4b602 (md5 0648e5f8…), while origin's note is at f34e9c0b1 (md5
c909343e…). Following the protocol, only sentences whose text I verified at the tip are keyed, in
`metadata/sk-census-rows/ms-intro-2.tsv`:
- `66cb283340f3` "Finally, ξ ↦ diag(u_ξ,1,1) is an injective homomorphism Λ → GL_3(R_Δ)." formalized.
- `cbce9a479de2` "So G_Δ contains Γ ≤ [Δ,Δ] ≤ [Λ,Λ]." formalized.
- `816030a10c14` "It maps [Λ,Λ] into G_Δ, since over F_2 every unit v satisfies …" is not keyed yet. At f34e9c0b1 the product reads
  `v = v_1, v_2, (v_2v_1)^{-1}` instead of `c, c', (c'c)^{-1}`, so the hash changes. The carrier is unchanged
  (`printedLEFDiagonalIdentities`, `lefDiagonalHom_commutator_le`), and the row lands when skf-census regenerates.
