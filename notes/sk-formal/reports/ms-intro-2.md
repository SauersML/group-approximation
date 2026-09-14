# Lane ms-intro-2 (SK note): "LEF groups", part (iv) of the proof of cor:lef

Target: the note at tip 9047d0d3c. Rows are keyed by the 12-hex sentence hash of `metadata/SK_SENTENCE_CENSUS.tsv`. Brief:
ct/ROSTER-sk.md, "LEF LANES 21:22".

CLAIM part (iv) (21:3x), census l.332–345 and tip l.337–346, in the new module
`GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFDiagonalCommutators.lean`:
- the two displayed identities: the first over a ring with `2 = 0`, together with its signed form over every ring, and
  the second over every ring;
- `ℓ ↦ diag(u_ℓ,1,1)`: an injective homomorphism `L →* GL₃(R)` for an injective `u : L →* Rˣ`, over any unital ring,
  so that sk-lef-action's crossed product `LC(Z,F₂) ⋊ L` plugs in;
- the image of `[L,L]` lies in `EL₃(R) = elementaryGroup (Fin 3) R`;
- `[Δ,Δ] ≤ [L,L]` for `Δ ≤ L`, and `Γ ≤ [L,L]` from `Γ ≤ [Δ,Δ]`, which is part (i) (sk-lef-ultra).

Consumes `Leavitt/ElementaryGroup` (`elementaryUnit`, `elementaryGroup`) and `KOne/BlockWhitehead` (`diagAtHom`,
`diagPairAt_self_inv_mem`, `diagAt_commutator_mem`).

| hash | census tex | sentence | status | carrier |
|---|---|---|---|---|
| 58f4e8dc5ed5 | 332 | "Finally, `ℓ ↦ u_ℓ` embeds `L` in `GL_1(R)`." | open (claimed) | the injective `u : L →* Rˣ`, a hypothesis here; sk-lef-action produces it |
| 36fec8cc638b | 334–342 | display: the two diag identities (with "Over F₂, for units a,b,c of R") | open (claimed) | LEFDiagonalCommutators |
| 17c59a49b0ee | 343–345 | "So `ℓ ↦ diag(u_ℓ,1,1)` is an injective homomorphism … and `Γ ≤ [Δ,Δ] ≤ [L,L]`." | open (claimed) | LEFDiagonalCommutators |
