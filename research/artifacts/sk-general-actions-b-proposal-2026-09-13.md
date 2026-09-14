# Proposal from lane sk-general-actions-b: a dichotomy sentence beyond Z?

Lane `sk-general-actions-b` (SK swarm), 2026-09-13. The question in the brief: is there a one-line sharp dichotomy the note should carry, such as "G_X is LEF iff X has periodic pattern approximations, and for Z always"? Line numbers refer to `$SK/manuscript-disk-1646.tex`.

## Recommendation

**Option 0 (recommended): no change.** The note should not carry a dichotomy sentence. Reader-facing reasons:
1. **For Z the equivalence is empty.** Every infinite minimal subshift has periodic approximations (l.123-129), so "LEF iff periodic approximations" says nothing about the note's groups.
2. **Beyond Z the sharp form is not a short true statement.** The equivalence LEF ⟺ matricial ⟺ invariant measure ⟺ residually finite is proved only for virtually free acting groups. It needs rank N ≥ 4 and rests on Kerr–Nowak Theorem 5.2 plus results that are not in the literature. The reader would need machinery the note does not otherwise carry and facts they cannot check against a source.
3. **The group-level form is conjectural.** "Z is, up to finite index, the only acting group for which every free minimal subshift works" follows from the Carroll–Penland conjecture (artifact part 1 §3). A note should not end on a conditional framing of its own hypothesis.

**Option 1 (only if the note adopts a generality remark from sk-general-actions-a): one flat limitation sentence.** Suppose the note gains a remark that the proof works for a minimal free subshift over any finitely generated group whose windows are realized exactly by finite Γ-sets. Then the reader benefits from one sentence saying where the hypothesis fails. It needs no machinery and proves itself.

(a) Current text: no such sentence exists. The remark would follow the proof of Theorem 1, after l.227. Proposed addition, to be appended to sk-general-actions-a's remark:

```latex
Over $\Z^2$ such finite models do not exist for subshifts of aperiodic tilings,
since a periodic configuration with the same windows as $X$ would be a periodic tiling.
```

(b) Proof as it would appear: the sentence carries its own proof. For a window W containing the matching rules of the tile set, a configuration whose W-windows are windows of X satisfies the matching rules. So a periodic configuration with those windows is a periodic tiling, which aperiodicity excludes.

(c) Length: +2 lines, and only together with the generality remark.

(d) Reader trade-off: it tells the reader exactly where Z is used and that the extension beyond Z is not automatic, at the cost of two lines and no new machinery or unverified fact.

(e) Status: the fact is `sfts-without-finite-orbits-are-not-residually-finite-actions` (established) and, in finite-model form, `window-lef-subshifts-give-matricial-crossed-products` item 4 plus the Labbé model test (unreviewed).

**Option 2 (not recommended): a general-Γ theorem with a window-LEF hypothesis and the virtually cyclic conjecture.** This costs about 8-10 lines plus a definition, and part of the content is conjectural. It fails the length constraint for a short note. The mathematics lives in Cairn instead.

## What this lane established for Cairn (unreviewed)

- `free-rf-actions-force-residually-finite-groups`: free RF actions force RF acting groups.
- `window-lef-subshifts-give-matricial-crossed-products`: partial finite models exact on windows give matricial crossed products and LEF GL_M over finite fields. For finitely presented Γ this is window periodicity.
- `generic-rotation-codings-of-zd-are-window-periodic`: a concrete Z^d family beyond Toeplitz and products. Its contrast with Labbé's Markov-partition coding shows that qualification depends on partition geometry.
- Open: `free-minimal-subshifts-all-rf-iff-virtually-cyclic` and `free-minimal-subshift-el-groups-all-lef-iff-virtually-cyclic`. (⇐) is proved for both. (⇒) is proved for non-RF (resp. non-LEF) groups, for groups with weakly aperiodic SFTs (resp. groups containing F_2), and reduced to Carroll–Penland (resp. the Labbé decider).

## Sharpest next target

For Z², does "not residually finite" imply "not exactly matricial" for free minimal subshifts? This is the quantum-to-classical question for periodic torus tilings. A proof would make the LEF version of the virtually cyclic conjecture follow from Carroll–Penland for amenable groups. A counterexample, a periodic quantum tiling of an aperiodic tile set at every scale, would give simple Kazhdan LEF groups from subshifts with no periodic approximations. Owner on main: the Labbé ring nodes. It deserves a family of lanes only after sk-fp-sofic-b reports.
