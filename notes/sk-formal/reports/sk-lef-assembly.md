# Lane sk-lef-assembly: `simple_kazhdan_sofic_group.tex`, section "LEF groups", cor:lef statement and assembly

Lead: session nonsofic-existence-49 (ROSTER-sk, "LEF LANES 21:22"). Target: origin/main tip of the note, 9047d0d3c (20:31),
618 lines, md5 274f19367f7f706b05c017af721c3884. Census rows are keyed by 12-hex hash once skf-census regenerates at this md5.

## CLAIM

CLAIM cor:lef statement and assembly GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFCharacterization.lean

Ownership check at 21:3x: no declaration on origin, on the shared tree or in `lanes/*.files` names a LEF characterization,
`PrintedLEFSubgroupCharacterization`, or a module `LEFCharacterization`. `isLEF_of_injective` (`Sofic/LEF.lean`) is the landed
heredity lemma and is consumed by name.

## Split agreed with ms-intro-3 (its message, ~21:30)

- This lane owns the statement Props and their closure. ms-intro-3 writes no Lean for abstract l.37–40 or intro l.89–93.
- ms-intro-3 lands the census rows for abstract l.37–40, intro l.89–90 (structural, roadmap to Part (ii)) and intro l.90–93 (the
  conjunction of this lane's cor:lef endpoint with sk-universal's second corollary).
- Names adopted verbatim from ms-intro-3's proposal: `PrintedLEFSubgroupCharacterization` and, once closed,
  `printedLEFSubgroupCharacterization`.

## Ledger (tip 9047d0d3c, section "LEF groups", l.267–279 and the proof's architecture)

| l. | sentence (abridged) | grade (planned) | carrier / owner |
|---|---|---|---|
| 269–270 | Every countable group embeds in a finitely generated simple group [Gorjuskin, Schupp]. | attribution | prior work, not used as a step |
| 270–272 | Kionke and Schesler proved that every f.g. RF group embeds in a f.g. simple LEF group [Theorem 1.2]. | attribution | prior work, not used as a step |
| 272–273 | The next corollary adds property (T) and applies to every LEF group. | structural | roadmap, carried by cor:lef |
| 273–274 | Since LEF passes to subgroups, it characterizes LEF groups. | formalized (heredity) + partial (characterization) | `printedSubgroupsOfLEFAreLEF`; `PrintedLEFSubgroupCharacterization` below |
| 276–279 | cor:lef: A f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group. | partial | `PrintedLEFSubgroupCharacterization`, `printedLEFSubgroupCharacterization_of_pieces` over the two piece Props below |
| 282 | Subgroups of LEF groups are LEF. | formalized | `printedSubgroupsOfLEFAreLEF` (closed, over `isLEF_of_injective`) |
| 282–292 | Part (i): Γ ↪ Δ = Δ₀ × ℤ, infinite f.g. LEF, Γ ≤ [Δ,Δ] | owner sk-lef-ultra (with sk-ore) | piece Prop `LEFUltraproductEmbeddingStatement` |
| 294–346 | Parts (ii)–(iv): G = EL₃(LC(Z,F₂) ⋊ L) is infinite, f.g., simple, Kazhdan, LEF, and [Δ,Δ] ↪ G | owners sk-lef-action, sk-lef-simplicity, sk-lef-models, ms-intro-2 | piece Prop `LEFLamplighterStatement` |

## Piece Props (the interface the piece lanes produce)

- `LEFUltraproductEmbeddingStatement` (Part (i), l.282–292): every f.g. LEF group `Γ : Type` admits an injective homomorphism into
  an infinite f.g. LEF group `Δ : Type` whose image lies in `commutator Δ`.
- `LEFLamplighterStatement` (Parts (ii)–(iv), l.294–346): every infinite f.g. LEF group `Δ : Type` has an infinite f.g. simple
  Kazhdan LEF group `E : Type` and an injective homomorphism `commutator Δ →* E`.
- The finer split for the concrete `E = EL₃(LC(Z,F₂) ⋊ L)` (FG, (T) and infinite; simple; LEF; `[L,L] → E` with Δ ≤ L) is
  assembled into `LEFLamplighterStatement` over sk-lef-action's construction once its definitions land. Until then the piece
  lanes keep their own named Props for the concrete group.

## Status

- 21:3x: claim landed; module written, probing.
