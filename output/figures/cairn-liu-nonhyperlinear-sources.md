# Sources and status conventions

This is a focused explanatory figure, not a raw export of the entire Cairn graph. It condenses internal proof steps and overlays Liu's claimed results. It does not modify or certify any research-node status.

- `research/kt-pair-non-hyperlinear-commutant.md`: route whose target is `non-hyperlinear-group` and whose prerequisite is `kt-centralizer-normalization-hs`.
- `research/kt-centralizer-normalization-hs.md`: open normalization claim and the lamp contradiction.
- `research/leavitt-channel-rounding-forces-nonhyperlinearity.md`: established conditional theorem, including the narrower Kazhdan heat-rounding premise and the connection to commutant internality.
- `research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md`: two-use heat argument and internality interface.
- `research/non-hyperlinear-group.md`: open root goal.
- Commit `516e496a4a`, `research/kun-thom-lamp-wreath-is-not-hyperlinear.md`: Liu's claim recorded as OPEN, under review. This commit is later than the current working checkout.
- J. Liu, *Nonhyperlinear groups exist*, dated 20 September 2026: §§3–4, Theorem 5.1, Lemma 5.4, Lemma 6.4, Propositions 6.5–6.6, Theorems 6.7 and 7.4. Paper source: https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf . The saved local copy was inspected.

The Leavitt conclusion is a proposed downstream application, not a theorem asserted by this figure. The broad conjecture on all near-idempotent bistochastic channels is deliberately omitted: Liu's claimed Kazhdan-commutant theorem does not by itself assert that broader conjecture.

The installed `tools/cairn.py` provides a static-site generator, textual dependency trees, and a `preview` command for working-tree research-state differences. No diagram-export command was found in that installed version or the local `/Users/user/Cairn` checkout.

The editable diagram source is `cairn-liu-nonhyperlinear.dot`. Graphviz renders the SVG and PNG versions.
