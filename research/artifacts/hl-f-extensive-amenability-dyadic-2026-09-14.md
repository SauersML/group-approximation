# hl-f-extensive-amenability-dyadic: the inverted-orbit target for extensive amenability of F ↷ D

Lane date: 2026-09-14. Unreviewed. Executes the top survivor of `ideas-wildcards`
(`thompson-f-dyadic-action-is-extensively-amenable`, from `600f96561`). Verdict: **not decided**. No
proof that `F ↷ D` is or is not extensively amenable, so `thompson-f-is-amenable` and the
Aiello–Brothier–Conti question (arXiv:1901.10597, Remark 4.7) both stay open. What is landed: the exact
probabilistic target, and a theorem that the standard recurrence route to it provably fails.

## Sources read at source (2026-09-14)

- **[JMBMdlS18]** K. Juschenko, N. Matte Bon, N. Monod, M. de la Salle, *Extensive amenability and an
  application to interval exchanges*, arXiv:1503.04977 (ETDS 38 (2018) 195–219). arXiv source
  `extAmen2.tex` fetched and read. Used verbatim:
  - Definition 1.1 (extensive amenability); Lemma 2.1 (amenable ⇒ ext. amenable ⇒ amenable).
  - Proposition (§"The inverted orbit"), conditions (i)–(iii), the μ/x₀-independence, and the
    switch-walk-switch identity `P(f_n = f_0) = E(2^{−|O_n|})` inside its proof.
  - Theorem (JNS Thm 1.2): recurrent actions are extensively amenable.
  - Lemma (Bartholdi–Erschler; Amir–Virág): `G ↷ X` recurrent iff `(1/n)E|O_n| → 0`; and the identity
    `(1/n)E|O_n| → P(T = ∞)`.
- **[Mi15]** P. Mishchenko, arXiv:1512.03083: the dyadic Schreier graph has nontrivial Poisson boundary,
  hence is transient. Relied on via the existing pin in the target node; not re-read this lane.
- Existing nodes on main: `jones-subgroup-cosets-form-a-parity-lamplighter`,
  `affine-lamplighter-amenable-iff-extensively-amenable`,
  `jones-subgroup-coamenable-from-extensive-amenability-proof`,
  `thompson-f-dyadic-action-is-extensively-amenable`.

## The inverted orbit

For a symmetric finitely supported `μ` on `F` with generating support, base point `x_0 ∈ D`, and left
random walk `g_n = h_n⋯h_1`, the inverted orbit is `O_n = {x_0, g_1⁻¹x_0, …, g_n⁻¹x_0} ⊆ D`. JMBMdlS prove
that extensive amenability of a finitely generated transitive action is equivalent to each of:

- (i) `−(1/n) log E(2^{−|O_n|}) → 0`;
- (ii) for every `ε > 0`, `P(|O_n| < ε n) > e^{−ε n}` infinitely often;
- (iii) an events version;

and these are μ/x₀-independent. `F ↷ D` is transitive (matching leaf endpoints of equal-leaf-count
subdivisions) and `F = ⟨x_0,x_1⟩` is finitely generated, so the proposition applies. This is the landed
equivalence `f-dyadic-ea-iff-inverted-orbit-confinement` (+ item 4, the switch-walk-switch return
probability on `(Z/2)^{(D)} ⋊ F`).

## The recurrence route provably fails

The recurrence criterion needs the strictly stronger `(1/n)E|O_n| → 0`. But the dyadic Schreier graph is
transient (Mishchenko), so `P(T = ∞) > 0` and `(1/n)E|O_n| → P(T = ∞) > 0`: the mean inverted orbit is
**ballistic**. This is the landed theorem `f-dyadic-action-is-not-recurrent`. It upgrades the target
node's informal "the recurrence criterion does not apply" into the quantitative statement that the mean
confinement condition fails outright. So the only inverted-orbit route left is the rare-event condition
(ii), landed OPEN as `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`, with the route
`f-dyadic-ea-from-inverted-orbit-confinement` into the target.

## Positive-side attempts (not landed; recorded here)

- **Følner sets on the parity lamplighter.** Condition (ii) can in principle be met by exhibiting, for each
  `ε`, an event of probability `≥ e^{−εn}` on which the inverse trajectory `g_k⁻¹ x_0` stays within `o(n)`
  distinct dyadics. Natural candidate events: the walk `g_n` staying inside a subgroup whose action on the
  relevant sub-orbit is recurrent (e.g. a copy of `F_{[a,b]}` acting on dyadics of a subinterval), or the
  trajectory confined to a bounded-depth band `{t : ℓ(t) ≤ Cn}`. The obstruction is that the branching of
  the dyadic Schreier graph makes any bounded-depth confinement cost an exponential probability with a rate
  that does not go to `0` with the band, so a single band does not beat every `ε`. A multi-scale nesting of
  bands (bands of geometrically increasing depth entered for geometrically increasing times) is the natural
  next construction; it was not carried to a bound.
- **Why the transient mean does not settle it.** Ballistic mean is compatible with (ii): a transient walk
  can still spend `e^{−εn}`-probability excursions confined to few sites. The question is exactly a
  large-deviation / cogrowth estimate for the dyadic lamplighter and is of the same difficulty as the
  unsettled `(8 + 4√3)^n` cogrowth numerics for `F` (Cleary–Elder–Rechnitzer–Taback, arXiv:0711.1343).

## Exact gap

`f-dyadic-inverted-orbit-is-subballistic-on-rare-events` (condition (ii)). A subexponential lower bound
`E(2^{−|O_n|}) ≥ e^{−o(n)}` proves co-amenability of Jones' subgroup; a genuine exponential upper bound
proves `F` nonamenable. Nothing here decides which. The multi-scale band construction and a matching
spectral-radius upper bound for `(Z/2)^{(D)} ⋊ F` are the two open ends.

## Checks

No heavy compute. MSI was up (pid 22224) at the start; only the JMBMdlS source and a Cairn `why` were run
there. No numerics were needed for the landed statements, which are citations plus the transitivity check
and the Mishchenko combination.
