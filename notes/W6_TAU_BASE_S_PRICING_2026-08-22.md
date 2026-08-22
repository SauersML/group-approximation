# W6: pricing `τ` and the base case `S`

Written 2026-08-22 for the two W6 leaves that had no construction on record.
Both were assigned as "design first, then formalize what is reachable".

> **Headline.**  The two leaves are *not* comparable in cost.  The base case
> `S` is **cheap and now proved** — it needs no new group at all, only the
> tower `Higman.FlipGroup` already builds, because Higman's `S` happens to be
> a *two-sided translation orbit*.  `τ` is **not** cheap: every route that
> lives inside `F₃` is refuted (a Lean-level refutation is included, strictly
> stronger than the two-letter witness on record).  What is left, after the
> reductions below, is **one finitely generated subgroup carrying a basis
> permutation** (§2.7) — not a five-stage tower, and not a classical input.

Files:

* `GroupApproximation/Higman/SwapWitnessTower.lean` — the `τ` interfaces, the
  refutation, and the three reductions that shrink what `τ` still owes.
  Written, final, and the only Lean file this memo's author owns.
* Base `S` is **designed here (§1) but not landed by this memo**, and is
  reassigned to `strike-base-s`.  The first attempt was written to the path
  `Higman/BaseCaseS.lean`, which on this repository's **case-insensitive**
  filesystem is the same file as `Higman/BaseCases.lean` — it truncated
  Higman's base case `Z`, and was reverted with
  `git checkout HEAD -- GroupApproximation/Higman/BaseCases.lean`.
  **Whoever lands base `S` must choose a filename differing from `BaseCases`
  by more than case** (e.g. `BaseCaseSucc.lean`); the design in §1 is
  unaffected and is being reused.

---

## 0.  Summary table

| leaf | status after this pass | new inputs it still needs |
|---|---|---|
| base `S` (`OperationClosures.base`) | **design complete, cheap, not landed by this memo** (reassigned to `strike-base-s`) | none mathematically — §1 needs no new group and no classical input |
| `τ` (`OperationClosures.tau`) | reduced to one finitely generated carrier | a f.g. `L` inside a f.p. torsion-free `K ⊇ F₃`, containing every `a_f`, with an automorphism performing `f ↦ τ f` on them (§2.7) |

`ClosuresAssembly.operationClosures_of_inputs` takes six inputs; `hbase` is
now dischargeable by `Seq.benignTF_ASub_Sset`, leaving five.

---

## 1.  Base case `S`: the design, and why it is cheap

### 1.1  The observation

Higman's `S = {(n, n+1) : n ∈ ℤ}` is `Seq.Sset = Set.range Seq.succSeq` with
`succSeq n = single 0 n + single 1 (n+1)`.  Its coding is

    b_{succSeq n} = r₀ⁿ r₁ⁿ⁺¹        (r_i = Seq.rowElt i = c⁻ⁱ b cⁱ),

which is `Seq.elt_window` at a sequence supported in `[0, 2)`.  The whole
design rests on one line of arithmetic:

    r₀ · (r₀ⁿ r₁ⁿ⁺¹) · r₁ = r₀ⁿ⁺¹ r₁ⁿ⁺² ,      i.e.   b_{n+1} = r₀ · b_n · r₁ .

So the index family `{b_n}` is an orbit of a **two-sided translation** of the
index set `K`: left by `r₀`, right by `r₁`.  Nothing about `S` is
order-sensitive, and no machine is simulated.

### 1.2  Why that is free

`Higman.FlipGroup` already builds `G₂ = F₃ ⋊_ψ K = N ⋊ (K × K)`, finitely
presented (`Flip.isFinitelyPresented_G₂`) and torsion-free
(`Flip.torsionFree_G₂`), in which

* right translation of the index is conjugation by `emb v⁻¹`
  (`a^w ↦ a^{wv}`, trivially, since `emb` is a homomorphism), and
* left translation is conjugation by `f0 u` for `u ∈ K`
  (`a^w ↦ a^{uw}`) — this is `Flip.conj_left` plus `Flip.conj_f0_emb`.

So the *whole* group of two-sided translations `w ↦ u w v` is realised by
conjugation in `G₂`.  The element

    g = f0 (r₀) · (emb r₁)⁻¹              (`Seq.succShift`)

satisfies `g · emb (a_{succSeq n}) · g⁻¹ = emb (a_{succSeq (n+1)})` for every
`n ∈ ℤ`.  `G₂` was built for `ρ`; it pays for `S` as well, at no extra cost.

### 1.3  The rest is `Row.comap_Lsub`, transcribed

With `L = ⟨emb a_{succSeq 0}, g⟩` (two generators) the argument is exactly the
collecting process of `Higman.RowSubgroup`:

1. `M = (A_S).map emb` is normalised by `g` (both directions, since
   `g⁻¹ · a_{b_n} · g = a_{b_{n-1}}`);
2. therefore `{m gᵏ : m ∈ M, k ∈ ℤ}` is a subgroup containing both generators,
   so it contains `L`;
3. a stable-letter grading `λ : G₂ → Multiplicative ℤ` kills `emb F₃` and
   sends `g` to `ofAdd 1`, so an element of `L` that lies in `emb F₃` has
   `k = 0`, hence lies in `M`;
4. `L.comap emb = A_S`, and `BenignWitness`/`TorsionFreeBenignWitness` close.

The grading in (3) is the one new gadget and it is three lines: `G₂` is an HNN
extension of `G₁` whose associated subgroup `Acopy` is the copy of `F₃`, on
which the *first* stage's grading `HNNTorsionFree.lengthHom psiBTop` is
constant `1`; so that grading lifts through `HNNExtension.lift` with stable
letter `1`.  It counts the `β`-letters, and `g` has exactly one because
`rowElt 0 = b` and `f0 b = beta`.

### 1.4  Cost, realised

≈ 330 lines, no new classical input, no `TorsionFreeImageClosure`, no amalgam,
no Britton induction.  A full draft at that length was written and then lost to
the filename collision described in the header; it was never elaborated, so
nothing is claimed for it beyond the design.  Risk is transcription risk only,
and the three steps most likely to need adjustment are the `group` call that
moves a `zpow` across a `+ 1` (§1.1's arithmetic), the `Finsupp.filter_apply`
`if`-instances in the `lowPart`/`highPart` lemmas, and the placement of the
module *downstream* of `Operations` and `FlipGroup` (it consumes `succSeq`,
`Sset`, `Flip.conj_left` and `Seq.elt_window`, so it cannot be `BaseCases`
itself without a cycle).  `rowElt 0 = b` already exists as
`Omega.rowElt_zero`; do not redeclare it.

### 1.5  What the sources say, and why this is not what they do

Both sources prove `S` on the `d`-side, inside `⟨a, d, e⟩`, where `a_f` is
indexed by a *weight vector* and the successor family is handled by the same
apparatus as everything else in §4.  That is the right thing to do if the
apparatus exists; it is the wrong thing to do here, where the apparatus does
not exist and the repository's coding is `F₃`-native.  The `F₃`-native route
above is not in either source, and the reason it works — that `S`'s index
family is a two-sided translation orbit — is special to `S` and does **not**
generalise to the other operations.  `BaseCases.lean`'s own docstring
anticipated a "two-stable-letter extension whose base is `F₃`"; `G₂` *is* a
two-stable-letter extension whose base is `F₃`, so that prediction was right,
and the extension is already built.

---

## 2.  `τ`: what is actually required

### 2.1  The demand, restated

`Seq.SwapWitness` asks for a f.p. torsion-free `G ⊇ F₃` and an element
conjugating `a_f` to `a_{τf}` for every `f`.  Writing `b_f = X r₀ᵖ r₁^q Y`
with `X` below the window and `Y` above (`Seq.bElt_tauSeq`), the required map
on the free basis `{a^w : w ∈ K}` of the normal closure of `a` is

    X r₀ᵖ r₁^q Y  ↦  X r₀^q r₁ᵖ Y ,

the identity outside the sorted normal forms.  This is *not* a two-sided
translation and *not* an inversion, so — unlike `S` and unlike `ρ` — `G₂` does
not reach it.  The realisable index maps in `G₂` are exactly
`w ↦ u w v` and (via the flip automorphism) `w ↦ (u w v)⁻¹`; the group they
form is `(K × K) ⋊ ℤ/2` acting on `K`, and `τ`'s map is in it for no choice of
`u, v`.

### 2.2  Three refutations, in increasing strength

1. **On record** (`research/mikaelian-rho-tau-shortcuts-fail.md`): the
   free-group automorphism swapping `b₀` and `b₁` sends `b₀b₁` to `b₁b₀`, not
   to `b₀b₁`; the two-letter witness `f(0) = f(1) = 1` kills it.
2. **Proved here** (`Seq.not_tau_of_endomorphism`, in
   `SwapWitnessTower.lean`): *no* endomorphism `ψ` of `F₃` with `ψ a = a` that
   maps `K` into `K` satisfies `ψ (a_f) = a_{τf}` for all `f`.  The proof does
   not assume `ψ` is the letter swap — it **derives** it: `f = single 0 1`
   forces `ψ r₀ = r₁` and `f = single 1 1` forces `ψ r₁ = r₀` (by
   `Seq.conj_a_inj`, i.e. `cbHom` injectivity), after which the two-letter
   witness applies.  So the whole endomorphism family, not one member of it,
   is dead.
3. **The repair is dead too** (argued here, not formalised).  The natural
   repair is to work modulo the centraliser: ask only that
   `Φ (emb b_f) = z_f · emb b_{τf}` with `z_f` centralising `emb a`.  That is
   the correct weakening (§2.3), *but* if `Φ` maps `emb F₃` into itself then
   `z_f ∈ emb F₃ ∩ C_G(emb a) = emb ⟨a⟩` — because `emb` is injective — and
   `f = single 0 1` then forces `r₀ r₁⁻¹ ∈ ⟨a⟩ ∩ K = 1`, i.e. `r₀ = r₁`.
   **Design constraint: any `τ` automorphism must move `emb F₃` off itself,
   and the centralising elements `z_f` must be genuinely new.**  This is the
   sharp reason Higman's proof lives in `⟨a, d, e⟩` and not in an overgroup of
   `F₃`.

### 2.3  Two reductions that shrink the obligation (both landed)

* **An automorphism suffices; an element is not needed.**
  `benignTF_of_aut` (already in `OperationClosureRho`) consumes an
  automorphism, and `ρ` uses it; `τ`'s structure asked for an element only
  because `benignTF_of_conj` was the shape in view.  `SwapAutWitness` and
  `Seq.benignTF_ASub_tauOp_of_swapAut` do the automorphism version, and
  `SwapWitness.toSwapAutWitness` shows the element version is a special case.
  This matters because the `d`-side construction produces an *outer*
  automorphism (a letter permutation), never an inner one.
* **The `transport` field is now free.**  Every witness structure in this lane
  carries `transport : ∀ H, BenignTF H → BenignTF (H.map emb)` as an open
  field.  `Seq.torsionFreeImageClosure` (proved, in
  `Higman/TorsionFreeImageClosure.lean`) discharges it at any embedding into a
  f.p. torsion-free group.  `Seq.transport_of_torsionFreeImageClosure` and
  `SwapAutWitness.ofAut` package that, so **`τ` now needs the construction and
  nothing else**: a f.p. torsion-free overgroup and one automorphism.
  (`ClosuresAssembly` already did the same bookkeeping for `ρ`.)

### 2.4  Route A — Higman's `d/e` apparatus (Mikaelian's tower)

The tower is `Λ₀ = K₀ ∗_{L₀} t`, `Λ₁ = K₁ ∗_{L₁} s`, `Θ = Λ₀ ∗_F Λ₁`,
`Ψ = Θ ∗_ω d`, `Δ = Ψ ∗_δ e`: two HNN extensions, one amalgam, two more HNN
extensions.  What it buys is Lemma 4.2, the *weight-vector property*: `a`'s
centraliser contains the derived group of `⟨d_i⟩`, so `a^{d-word}` depends
only on the weight vector, and the exponent swap becomes the letter swap
`d₀ ↔ d₁` — an honest automorphism, because order is now irrelevant.

Permanence is not the problem: HNN f.p. (`HNNFinitePresentation`), HNN
torsion-free (`HNNBritton.isPowerTorsionFree_hnn`), amalgam f.p.
(`Higman/AmalgamPresentation`) and amalgam torsion-free
(`Algebra/PushoutITorsionFree`, via `Amalgam.isPowerTorsionFree_push`) are all
proved here.  The cost is elsewhere:

* the five stages, with their associated subgroups and identifying
  isomorphisms stated and their f.g.-ness proved: **≈ 1200 lines** (calibrate
  against `FlipGroup.lean`, 676 lines for *two* stages with `⊤` and a copy of
  `F₃` as associated subgroups — the tower's subgroups are harder);
* Lemma 4.2 itself, a normal-form/Britton computation in a five-stage tower:
  **≈ 400–700 lines**, and this is the item with no precedent in the
  repository except `Higman/Pinch`;
* **the join to the repository's statement.**  This is the part the briefing
  and the notes both under-price.  `OperationClosures.tau` is stated
  `F₃`-natively, about `Seq.ASub`.  Higman's §4 proves closure for the
  `d`-side subgroups `⟨a^{δ_f} : f ∈ B⟩ ≤ Δ`.  Getting from one to the other
  is either
  * (A-i) a second coding `ASubD`, a proof that `A_B` and `A^D_B` are
    simultaneously benign, and the induction re-run — which drags *every*
    operation, not just `τ`, onto the `d`-side: **≈ 800+ lines and a new
    transport argument**; or
  * (A-ii) building `Δ` so that `F₃ ↪ Δ` *and* `a^{δ_f} = a^{b_f}` for the
    sorted `f` only.  §2.2(3) says this is not contradictory (no two distinct
    `a^{b_f}` are ever identified), but it is not in either source and the
    consistency of the resulting presentation would have to be proved by a
    normal-form argument of its own.

  Known obstruction inside route A, recorded so it is not rediscovered: the
  transposition `d₀ ↔ d₁` fixing all other `d_i` is an automorphism of the
  free group `⟨d_i⟩` but **does not extend to `⟨d, e⟩`**, because it does not
  commute with the `e`-conjugation that defines `d_i = e⁻ⁱ d eⁱ`.  This is the
  same obstruction `FlipGroup` met for `ρ` and solved by adjoining a second,
  commuting copy of `K`; expect the analogous extra stage here, and expect the
  source to have it.

  **Total for route A: 2500–3500 lines, and a source-verification duty that
  cannot be skipped** — §4's `τ` argument is not reconstructable from the
  repository's notes, and the two auxiliary Lemmas 4.1/4.3 are cited in the
  notes but never stated.

### 2.5  Route B — a bespoke overgroup (Mikaelian §4's "witness automorphism")

Ask directly for `WindowApparatus` (in `SwapWitnessTower.lean`): a f.p.
torsion-free `G ⊇ F₃`, an automorphism `Φ` fixing `emb a`, and for each `f` an
element `z_f` centralising `emb a` with `Φ (emb b_f) = z_f · emb b_{τf}`.
`WindowApparatus.toSwapAutWitness` proves this closes `τ`, so the interface is
sound.  Whether it is inhabited is open, and §2.2(3) says the inhabitant must
be strictly larger than anything the row calculus builds: `Φ` must move
`emb F₃`, and the `z_f` must be new elements.  The naive attempt — impose
`[r₀, r₁] ∈ C(a)` — is **refuted**: it collapses `F₃` (it forces
`a^{b_f} = a^{b_g}` for `f ≠ g`), contradicting injectivity of `emb`.

Honest price: **unknown, research-grade.**  No estimate should be quoted.

### 2.6  Route C — change the operation list

`HigmanGenerated` is the repository's own inductive, and Higman's §2
(`HigmanTheoremThree`, that every r.e. subset of the sequence space is
generated) is **input 2 of `FinalReduction` and is unwritten**.  So the real
obligation is *(the operations closed) + (§2 for those operations)*, and the
split between them is a free parameter.  Dropping or replacing `τ` moves cost
into §2 rather than removing it.

Two facts bound how far this lever moves.  With `σ` present, closure under
`τ = (0 1)` is equivalent to closure under any single adjacent transposition
`(n, n+1)`, and `⟨σ, τ⟩` acting on `ℤ` is the full finitary-permutation
extension of the shift — which is what a machine simulation needs in §2, so
`τ` is very unlikely to be droppable outright.  Conversely `τ` is *not*
derivable from `ρ` and `σ` alone: those generate the infinite dihedral group
on `ℤ`, every non-identity element of which is a fixed-point-free translation
or a reflection `i ↦ k − i`, and `(0 1)` is neither.  Whether `τ` is derivable
from the remaining *eight* (using `θ, ζ, π, ωₘ`, which are not
bijection-induced) is **open and not addressed in either source**; it is the
one cheap thing that has not been tried.

### 2.7  Route D — a finitely generated carrier (added after the ω-lane finding)

The ω-tower lane reports that Mikaelian's constructions are **multiple HNN
extensions whose stable letters act on a finitely generated subgroup** — the
centralizing case `ψ = id` being `Higman.CentHNN` — and that no genuine amalgam
appears, so `Algebra.PushoutITorsionFree` is not consumed by them.  That
re-prices route A's *stages* (each is an HNN, and both permanence theorems are
in the repository), and it also suggests the following sharper target, which is
now landed as `Seq.SwapCarrier` and `Seq.benignTF_ASub_tauOp_of_carrier`.

**The transposition is already an automorphism of `A_E = ⟨a_f : f ∈ E⟩`.**  The
`a_f` are a free basis (`Seq.aElt_injective`), and `f ↦ τ f` is an involution of
the index set (`Seq.tauSeq_involutive`), so it permutes that basis.  The HNN
extension of `F₃` along that automorphism therefore exists and is torsion-free,
and its stable letter *is* the element `Seq.SwapWitness` asks for.  The only
thing wrong with it is that `A_E` is not finitely generated, so the extension is
not finitely presented.

So `τ` reduces to: **a finitely presented torsion-free overgroup `K ⊇ F₃` and a
finitely generated `L ≤ K` containing every `a_f` and carrying the permutation
as an automorphism.**  Everything else is discharged:

* finite presentation of `HNNExtension K L L ψ` — `L` finitely generated,
  `HNNFinitePresentation.isFinitelyPresented_hnnExtension`;
* torsion-freeness — `HNNBritton.isPowerTorsionFree_hnn`;
* `swap_conj` — `HNNExtension.equiv_eq_conj`;
* `transport` — §2.3, free.

This is strictly more useful than `WindowApparatus` (§2.5) because it asks for a
*subgroup*, not an automorphism of a whole overgroup, and because a benign
witness **is** a finitely generated `L` inside a finitely presented `K`.
`Omega.benignTF_ASub_univ` already produces such a pair for `A_E` itself
(conditionally on `Omega.OmegaInput`, another leaf of the same six).  What
`SwapCarrier` asks on top of that witness is one automorphism of its `L`.

Note the base case `S` is this pattern one size down: there `L = ⟨a_{(0,1)}, s⟩`
and the automorphism is conjugation by `s`.  That is the sense in which `S` was
free and `τ` is not: for `S` the index family is a translation orbit, so the
carrier is two-generated and the automorphism is inner; for `τ` the index family
is all of `E` and the automorphism is a basis permutation with no translation
behind it.

**Price:** if the `A_E` carrier from `Omega.benignTF_ASub_univ` happens to admit
the automorphism, `τ` costs one lemma.  If not, it costs a bespoke benign
witness for `A_E` built to carry it — which is a construction of the same order
as `Higman.RowSubgroup` or `Higman.FlipGroup`, i.e. **hundreds of lines, not
thousands**, and an order cheaper than route A.  *This is the first thing to
try, and it did not exist before this pass.*

### 2.9  Recommendation

1. Land base `S` from §1 (assigned to `strike-base-s`; **not** at a path that
   collides with `BaseCases` under case-folding) and the `τ` reductions (landed,
   in `SwapWitnessTower.lean`).  That takes `OperationClosures` from six open
   inputs to five, and reduces `τ` from "construction + classical transport" to
   "one finitely generated carrier" (§2.7).
2. **Try route D first.**  Take the benign witness for `A_E` that
   `Omega.benignTF_ASub_univ` produces and ask whether its finitely generated
   `L` admits the basis permutation as an automorphism.  If it does, `τ` is one
   lemma.  If it does not, build a benign witness for `A_E` *designed* to carry
   it — a `RowSubgroup`-sized construction, not a tower.
3. **Do not start the `d/e` tower yet.**  Two things come first, and both are
   cheap: pin and *read* Higman §4 Lemmas 4.1–4.3 **and the `τ` closure proof
   itself** (4.4–4.10 range) — the repository has never had the `τ` argument,
   only the apparatus it is said to use; and spend one focused pass on route C
   (§2.6), which is the only route that could remove the apparatus entirely.
4. If the tower is started anyway, build it for `τ` *and* re-check whether it
   also subsumes `OmegaInput` and the three benign rows.  A five-stage tower
   that pays for one leaf is bad value; one that pays for four is the cheapest
   remaining path to `OperationClosures`.

---

## 3.  Corrections to the briefing

* "**base S: unpriced `F₃`-natively; the sources prove it d-side**" — correct
  as history, but the `F₃`-native proof turns out to be cheap and is now
  written.  It does not need the `d/e` apparatus, a new tower, or
  `TorsionFreeImageClosure`.
* "**`τ` … the only route in either source is Higman's `d/e` apparatus**" —
  correct, but the apparatus alone is not sufficient for the repository's
  statement: routes (A-i)/(A-ii) of §2.4 are an additional, unbudgeted item,
  and the `d₀ ↔ d₁` transposition does not extend to `⟨d, e⟩` without a
  further stage.
* "**`Seq.TorsionFreeImageClosure` … the coordinator is wiring its root
  import**" — noted; `Higman/ClosuresAssembly.lean` already imports it and
  already discharges `ρ`.  The `τ` files here assume nothing more.
* `Seq.SwapWitness` asks for an **element**.  The `d`-side construction
  produces an **outer automorphism**, so the element form is the wrong shape
  to aim at; `SwapAutWitness` is the right one.  `SwapWitness` is not wrong,
  just strictly stronger than needed (as `ClosuresAssembly`'s own docstring
  says of `operationClosures_of_swap`).
* `Higman/OperationClosureTau.lean`'s docstring says a swap "is the identity
  off the set of sorted normal forms, which is not the restriction of anything
  the row calculus produces".  That is now a theorem, in the stronger form of
  §2.2(2), and the docstring can cite `Seq.not_tau_of_endomorphism`.

## 4.  Transcription traps, carried forward

Unchanged and still binding: Lemma 2.8 is false as printed for `X = ∅` (carry
`Nonempty`); `σ³ζσ` in the `W`-construction is deliberate; the
`a(r) < 0 < b(r)` step needs the widened window at `h(r) = 0`; p. 464's local
`E` clashes with the sequence space.  Add one from this pass: **`ρ` in
Mikaelian's `ω_m` paragraph is the shift `a, b, c ↦ a, b^c, c`, not the
reflection** — the two are unrelated and the notes already flag it, but it is
the trap most likely to be hit by whoever builds the tower for `τ`, since both
appear within a page of each other.
