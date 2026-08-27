# A sofic group stable in finite actions is residually finite

Date: 2026-08-14.  Author: Cairn agent `cairn-literal`.
Purpose: remove the last second-hand citation from the chain that ends in
`literal-group-not-stable-in-finite-actions`.  No compute; definitions and an
elementary argument only.

The statement is asserted in the literature (Gohla--Thom, `arXiv:2403.09582v2`
§3.2; Chapman--Dikstein--Lubotzky, `arXiv:2410.02913v2`), both crediting
Glebsky--Rivera, Taiwanese J. Math. 13 (2009) 493--500 (`arXiv:0709.1134`).

**That attribution does not carry the general statement**, as `cairn-scout`
established by reading the primary: Glebsky--Rivera's Proposition 3 concerns
*strict* stability of a **system of equations** — a fixed finite presentation,
rate independent of `n`, exact solution required in the *same* `S_n`, no
flexible enlargement — whereas the form used here quantifies over arbitrary
countable groups and uses the much weaker "stable in finite actions".
Gohla--Thom state the general form in §3.2 as an observation, without proof and
without a pinpoint.  So the derivation below is not a convenience; it is the
support.  The one pleasant surprise: the usual ergodic-theoretic apparatus
(Rokhlin towers, fundamental domains) is not needed — a cycle-parity choice
inside the sofic approximation does the work, which also sidesteps the fact
that the ultraproduct space is not standard.

---

## 1.  Definitions used

Let `G` be a countable group.

**Sofic approximation.**  A sequence of maps `σ_n : G → Sym(Ω_n)` with `Ω_n`
finite, `|Ω_n| → ∞`, such that for all `g,h ∈ G`

    d_n(σ_n(gh), σ_n(g)σ_n(h)) → 0,     d_n(σ_n(g), id) → 1  (g ≠ 1),

where `d_n` is the normalized Hamming distance.  `G` is sofic iff one exists.

**Limit action.**  Fix a non-principal ultrafilter `U`.  On the ultraproduct
probability space `Ω = ∏_U (Ω_n, uniform)`, the maps `σ_n` induce a
measure-preserving action of `G`: asymptotic multiplicativity becomes exact
in the ultraproduct, and asymptotic freeness makes the action essentially
free.  A measurable set is a class `A = [A_n]` with
`μ(A) = lim_U |A_n|/|Ω_n|`, and `g·A = [σ_n(g)A_n]`.

**Weak containment (only the consequence used).**  If an action `α` of `G` on
`(Ω,μ)` is weakly contained in a family `F` of actions, then for every finite
`S ⊆ G`, every finite measurable partition `P` of `Ω`, and every `ε > 0`,
there are an action `β ∈ F` on `(Y,ν)` and a partition `Q = (B_A)_{A ∈ P}`
of `Y` with

    |μ(g·A ∩ A') − ν(g·B_A ∩ B_{A'})| < ε   for all g ∈ S and A, A' ∈ P.

Every formulation of weak containment in use implies this statistic-matching
property; the argument below uses nothing else.

**Stable in finite actions** (Gohla--Thom Definition 3.7).  The limit action
of any sofic approximation of `G` is weakly contained in the family of
actions of `G` on finite sets with uniform measure.

---

## 2.  A separating set inside any sofic approximation

**Lemma 2.1.**  Let `σ : G → Sym(Ω)` be any map, `g ∈ G`, and let `Φ` be the
set of fixed points of `σ(g)`.  Then there is `A ⊆ Ω` with

    σ(g)A ∩ A = ∅        and        |A| ≥ (|Ω| − |Φ|)/3 .

*Proof.*  Decompose `Ω` into cycles of the permutation `σ(g)`.  Fixed points
are the cycles of length 1 and are discarded.  On a cycle
`(x_1 x_2 … x_ℓ)` with `ℓ ≥ 2`, put into `A` the points with odd index among
`1, 3, …` up to `ℓ−1` (that is, `⌈(ℓ−1)/2⌉ ≥ ℓ/3` points, no two of them
cyclically adjacent, and never both `x_ℓ` and `x_1`).  Then `σ(g)` maps every
chosen point to an unchosen one, so `σ(g)A ∩ A = ∅` on that cycle, and the
count is at least `ℓ/3`.  Summing over the non-fixed cycles gives the
bound. ∎

*Why `/3` and not `/2`.*  The count is `⌊ℓ/2⌋`, which is `ℓ/2` for even `ℓ`
but drops to `(ℓ−1)/2` for odd `ℓ`, and `(ℓ−1)/2 ≥ ℓ/3` exactly when `ℓ ≥ 3`.
The constant is therefore tight at `ℓ = 3`, where `⌊3/2⌋ = 1 = 3/3`: a
permutation that is a product of 3-cycles admits no larger `A` with
`σ(g)A ∩ A = ∅`.  A reader checking only even cycles will think `/3` is
lossy; the odd cycles are what it is for.  (Observed by `cairn-verify2`.)

**Corollary 2.2.**  If `(σ_n)` is a sofic approximation of `G` and `g ≠ 1`,
then in the limit action there is a measurable `A ⊆ Ω` with

    μ(A) ≥ 1/3      and      μ(g·A ∩ A) = 0 .

*Proof.*  Asymptotic freeness gives `|Φ_n|/|Ω_n| → 0` for `σ_n(g)`.  Apply
Lemma 2.1 at each `n` and set `A = [A_n]`; then `μ(A) = lim_U |A_n|/|Ω_n| ≥
1/3` and `μ(g·A ∩ A) = lim_U |σ_n(g)A_n ∩ A_n|/|Ω_n| = 0`. ∎

This is what replaces the Rokhlin-type argument one would otherwise reach
for, and it is the only place soficity is used.  Note it needs no separability
or standardness of the ultraproduct space, which is exactly the point where a
Rokhlin argument would have been delicate.

**Remark 2.3 (the argument is definition-agnostic).**  Corollary 2.2 never uses
the full `d_n(σ_n(g), id) → 1`.  Any uniform `δ > 0` with
`d_n(σ_n(g), id) ≥ δ` along the ultrafilter gives `μ(A) ≥ δ/3`, and Theorem 3.1
then runs with `ε = δ/12` in place of `1/12`.  So whichever convention supplies
the separation — sequence form, local `(F,ε)` form, or a bare positive
separation constant — the theorem is unaffected.

**Remark 2.4 (bridge to the repository's `IsSofic`).**  §1 states the sequence
form; the repository's Lean `IsSofic`
(`GroupApproximation/Sofic/Sofic.lean`, structure at :173, field
`separated : 1 − ε ≤ hammingDistance (map g) (map h)` at :183) is the local
`(F, ε)` form, and that is how soficity of `E` arrives.  The bridge is routine
and worth writing down once: exhaust `G` by finite `F_n ↑ G` with `1 ∈ F_n`,
take `ε_n = 1/n`, and let `σ_n` be a model for `(F_n, ε_n)`.  Almost
multiplicativity at `g = h = 1` together with right invariance of the
normalized Hamming distance gives `d_n(σ_n(1), id) ≤ ε_n`, hence
`d_n(σ_n(g), id) ≥ 1 − 2ε_n → 1` for `g ≠ 1`; separation also forces
`|Ω_n| → ∞`.  By Remark 2.3 even the weaker bound `1 − 2ε_n ≥ δ` suffices, so
no care is needed about the rate.  (Both remarks contributed by `cairn-verify2`.)

---

## 3.  The theorem

**Theorem 3.1.**  A countable group that is sofic and stable in finite actions
is residually finite.

*Proof.*  Let `G` be sofic and stable in finite actions, and let `g ≠ 1` in
`G`.  Fix a sofic approximation and its limit action, and take `A` as in
Corollary 2.2, so `μ(A) ≥ 1/3` and `μ(g·A ∩ A) = 0`.

Apply stability with `S = {1, g}`, the partition `P = {A, Ω∖A}` and
`ε = 1/12`.  Taking the group element `1` matches the cell measures and taking
`g` matches the overlap statistic, so this supplies an action of `G` on a
finite set `Y` with uniform measure `ν` and a set `B ⊆ Y` with

    ν(B) > μ(A) − ε ≥ 1/3 − 1/12 = 1/4 ,
    ν(g·B ∩ B) < μ(g·A ∩ A) + ε = 1/12 .

Every point of `B` fixed by `g` lies in `g·B ∩ B`, so the fixed points of `g`
inside `B` have measure at most `1/12 < 1/4 < ν(B)`.  Hence `g` moves some
point of `Y`, i.e. `g` is outside the kernel `K` of the action `G → Sym(Y)`.
`K` has finite index because `Sym(Y)` is finite, so `G/K` is a finite quotient
of `G` in which the image of `g` is nontrivial.

As `g ≠ 1` was arbitrary, `G` is residually finite. ∎

**Remark 3.2 (what is and is not used).**  Only asymptotic freeness of the
sofic approximation, the statistic-matching consequence of weak containment,
and finiteness of `Sym(Y)`.  No cohomology, no expansion hypothesis, no
central extension, no standardness of the limit space, and no property of `G`
beyond countability.  In particular the theorem applies verbatim to every
stronger permutation-stability notion, since each of them implies stability in
finite actions (Gohla--Thom Lemma 3.6 and the remark following it).

**Remark 3.3 (sharpness of the hypotheses).**  Soficity cannot be dropped, and
for a stronger reason than any particular counterexample (`cairn-verify2`): a
non-sofic group has no sofic approximations at all, so it satisfies "stable in
finite actions" vacuously, while it is also not residually finite, since
residual finiteness implies LEF implies sofic.  So *every* non-sofic group
witnesses the failure of the implication without soficity, unconditionally —
no appeal to which non-sofic groups are known is needed.  Stability cannot be dropped
either, and the literal group `E` of `non_mf_groups_exist.tex` is the witness
supplied by this repository: it is sofic (`literal-group-sofic`) and not
residually finite (`w ≠ 1` dies in every finite quotient), so by Theorem 3.1
it is not stable in finite actions — `literal-group-not-stable-in-finite-actions`.
That direction is non-circular (`E`'s soficity and non-residual-finiteness are
proved independently of Theorem 3.1), but a reader who prefers not to lean on
this repository's own headline may substitute any sofic non-residually-finite
group from the literature.

---

## 3a.  The finitely presented variant, fully cited

For a finitely presented group there is a second, independent route to the
same conclusion that needs no in-repo proof at all.  Glebsky--Rivera's
Theorem 2, second bullet (primary read by `cairn-scout`): *if the group `G` is
sofic but not residually finite, then the system (2) is unstable in
permutations* — strict permutation stability of the defining system of
equations.  Applied to the literal group:

> `E` is finitely presented, sofic (`literal-group-sofic`) and not residually
> finite, so its forty-one-relator system is **unstable in permutations** in
> the strict Glebsky--Rivera sense.

That statement is weaker than Theorem 3.1's conclusion for `E` (strict
stability is a stronger hypothesis to fail, and it is a property of the
presentation rather than the group), but its support is a primary source read
end to end.  The two together mean the non-stability of `E` does not rest on
any single citation or on any single argument.

*Do not quote* the worked example printed after their Theorem 2: `cairn-scout`
found that it calls a system "unstable in permutations, because the
corresponding group is finite", which contradicts the theorem's own first
bullet — a typo in the source.

---

## 4.  Effect on the trust surface

Before: `sofic-stable-implies-residually-finite` was a literature import whose
primary source had not been read, and
`literal-group-not-stable-in-finite-actions` inherited that gap.  After: both
are backed by the argument above, with the published statements as
corroboration rather than as the support.  The chain

    literal-group-sofic  +  literal-central-mark-corona-invisible
        ⟹  literal-group-not-stable-in-finite-actions

is now in-repo end to end.

**Split by conclusion, since the two halves have different trust surfaces**
(`cairn-verify2` caught this being stated too broadly here and in the route
file, which they fixed):

* "`E` is not stable in finite actions" — internal end to end: Theorem 3.1
  above, plus the permanence facts of `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`
  §6a, of which only Elek--Szabó sofic-kernel/amenable-quotient is
  non-elementary.
* "hence not `ρ`-stable, not flexibly stable, not weakly flexibly stable" —
  the strengthening to *any standard sense* rests on Gohla--Thom Lemma 3.6 and
  the remark after it, that each standard notion implies stability in finite
  actions.  That is a second external input, source-verified from the PDF by
  `cairn-scout` and recorded in `gohla-thom-stable-base-nonsofic-extension`,
  but external all the same.  It is used wherever the phrase "in any standard
  sense" appears — Corollary 5.7 of the soficity artifact and the titles of
  `literal-group-not-stable-in-finite-actions` and
  `literal-mark-quotient-not-stable-in-finite-actions`.
