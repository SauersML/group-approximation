# Route C verdict: is `τ` derivable, and is it droppable?

Written 2026-08-22, one focused round, after `Higman/SwapCarrierWitness.lean`
proved that every construction mechanism this repository has for a coded family
is excluded for `τ`.

> **Verdict.  `τ` is not derivable from the other eight in general — but it is
> DROPPABLE, and it is droppable today.**  `HigmanGenerated.tau` is spent in
> exactly four places in the repository.  Three are in `Higman/GeneratedValue`
> and every one of them is removable, by `σ` alone.  The fourth is in
> `Higman/HigmanVariableCalculus`, which **no module imports**, and whose
> `swapAt` has **no consumer anywhere in the repository**.  Rewriting the three
> `GeneratedValue` sites takes `τ` off the critical path of our chain entirely.

Lean that falls out: `Higman/TauRouteC.lean` — the replacement identity, the
`τ`-free proof of the pin at coordinate `1`, and the window-class derivation
that is the sharp limit of C1.

---

## C2.  Droppability — where `τ` is actually spent

`OperationClosures.tau` is consumed in exactly one place,
`Seq.benignTF_of_higmanGenerated` (`Operations.lean:170`), on the `tau`
constructor of the `HigmanGenerated` induction.  So `τ` is spent exactly when a
`HigmanGenerated` *derivation* uses that constructor.  A repository-wide grep
for `HigmanGenerated.tau` finds four uses, and no others:

| site | what it does | removable? |
|---|---|---|
| `GeneratedValue.lean:197` | `pinOne c = τ (pinZero c)` | **yes — `σ`** |
| `GeneratedValue.lean:188` | same, inside `higmanGenerated_singleZero`'s `pred` case | **yes — `σ`** |
| `GeneratedValue.lean:179` | reads the second component of `succSeq n` in the `succ` case | **yes — `ρ σ ρ` then `θ`** |
| `HigmanVariableCalculus.lean:583` | base case of `higmanGenerated_swapAt` | orphan; see below |

### The three live sites, and why `σ` replaces `τ` at all of them

`pinZero c = {f | f 0 = c}` and `pinOne c = {f | f 1 = c}` are *pins*: one
coordinate fixed, every other coordinate free.  Because `σ` is induced by a
**bijection** of the index set, `σ B = shiftSeq '' B` and `shiftSeq` is onto, so

    σ (pinZero c) = {shiftSeq g | g 0 = c} = {f | f 1 = c} = pinOne c .

That is `Seq.sigmaOp_pinZero` in `Higman/TauRouteC.lean`, and it immediately
gives `Seq.higmanGenerated_pinOne'`, a `τ`-free replacement for
`GeneratedValue.higmanGenerated_pinOne`.  Sites 197 and 188 are exactly this.

Site 179 is the one place `τ` does real work in the live chain: the `succ` step
of `higmanGenerated_singleZero` needs the value `n+1`, which sits at coordinate
`1` of `succSeq n`, moved to coordinate `0` so that `θ` (which reads
coordinates `2i`) can pick it up.  `τ` moves it; so does the **down-shift**,
which is available as `ρ σ ρ`:

    (ρ σ ρ) f  i = f (i + 1) ,      so   (ρ σ ρ) (succSeq n) = single 0 (n+1) + single (-1) n ,

and `θ` of that is `{single 0 (n+1)}`, because `2i` is never `-1`.  So
`θ (τ {succSeq n})` may be replaced by `θ ((ρ σ ρ) {succSeq n})` with the same
value and no `τ`.

**None of the three needs the transposition.**  What they need is a bijection of
the index set carrying coordinate `1` to coordinate `0`, and the infinite
dihedral group `⟨σ, ρ⟩` supplies one; the transposition is simply the wrong
tool, chosen because it is the operation whose *name* matches the intent.

### The fourth site is not in the chain at all

`HigmanVariableCalculus.higmanGenerated_swapAt` builds an arbitrary adjacent
transposition `swapAt d` from `τ` (the `d = 0` case) plus `σ`-conjugation.
That is W2's planned item (d), and it is the only place `τ` is genuinely
irreplaceable — `swapAt 0` *is* `τ`, by `tauOp_eq_swapAt_zero`.

But:

* `grep -rn "swapAt"` finds **no occurrence outside that file**;
* `grep -rln "HigmanVariableCalculus"` finds **no importer**.

So the module is an orphan and the transposition calculus is, today, unused
code.  `τ` is therefore not on the critical path of anything that currently
compiles or is currently wired.

### What this asks of the trace lane

The one decision that could bring `τ` back is the trace design.  If the
relations of the trace machine are composed in *different variable orders* and
then reconciled, arbitrary adjacent transpositions are needed and `τ` returns.
If each relation is built in a **canonical variable order** — tracks re-indexed
at encode time rather than permuted afterwards — they are never needed.

Two things say the canonical-order design is the natural one here.  First,
`Higman/HigmanAtoms` already builds the relational layer that way: `freeAt c`
(free any one coordinate), `freeAbove`, `freeBelow`, `succRel d`, `diffSet`,
`eqRel a b` are all constructed *at an arbitrary index* by `σ`-conjugation from
an index-`0` case, so the index is a parameter rather than something to be
permuted after the fact.  Second, `EnumeratedRangeTraceCorrectness` — the live
trace module — reaches `HigmanGenerated` without touching `swapAt`.

**Recommendation: state the requirement on the trace lane now, while the design
is open**: no relation may be consumed in a variable order other than the one it
is built in.  If they accept it, `OperationClosures` can be restated without the
`tau` field for our chain, and `τ` leaves the critical path permanently.

### What the restatement costs

Three edits in `GeneratedValue.lean` (not my file), and one field deleted from
`OperationClosures` (or a second constructor
`operationClosures_of_inputs_tauFree` alongside it, which is the safer shape
while `HigmanVariableCalculus` still exists).  Everything downstream —
`ClosuresAssembly`, `TheoremFour.reBenignTF_of_inputs`, `FinalReduction` — is
unaffected, because they consume the structure, not the field.

---

## C1.  Derivability — how far it goes, and where it stops

The honest answer is **partial, and the gap is precise**.

### What is derivable

On any set whose window values are pinned, `τ` is a composite of operations we
already have.  Write `W B` for `B` with coordinates `0` and `1` freed
(`freeAt 1 (freeAt 0 B)`, generated by `HigmanAtoms.higmanGenerated_freeAt`).
Then, for every `c, c' ∈ ℤ`,

    τ (B ∩ pinZero c ∩ pinOne c') = W (B ∩ pinZero c ∩ pinOne c') ∩ pinZero c' ∩ pinOne c

(`Seq.tauOp_windowClass` in `Higman/TauRouteC.lean`).  The proof is immediate
once stated: an element of the left side agrees with some `g ∈ B` off the
window and has window `(c', c)`; an element of the right side is exactly the
same thing, because membership in `B ∩ pinZero c ∩ pinOne c'` forces `g`'s
window to be `(c, c')`, so `g` is determined by its off-window part together
with the pins.  Only `ι`, `ζ`-conjugates and the pins appear — no `τ`.

So **`τ` is derivable on every set with bounded window values**, and in
particular on every finite union of window classes.

### Where it stops

The general case is

    τ B = ⋃_{(c, c') ∈ ℤ × ℤ} τ (B ∩ pinZero c ∩ pinOne c') ,

and the operation list has only the **binary** union `υ`.  There is no
countable union, and no operation in the list produces one.  So the derivation
above does not close, and the gap is exactly the uniformity in `(c, c')`.

### Why the obvious repair is circular

The standard way to make such a family uniform is to store the two window
values in auxiliary coordinates, permute, and copy back — using `eqRel a b`
(coordinates `a` and `b` agree) to do the copying.  That is precisely the
variable calculus of `HigmanVariableCalculus`, whose transposition step is the
one place `τ` is consumed.  Every attempt I made routed through a coordinate
permutation, i.e. back through `τ`.

I did **not** find a derivation, and I did **not** find a refutation.  What can
be said negatively is narrower than the two-sided theorem of
`SwapCarrierWitness` and worth recording as a bound on cheap attempts:

> `τ` is not derivable from `ρ` and `σ` alone.  Those are induced by index
> bijections and generate the infinite dihedral group on `ℤ`, every non-identity
> element of which is a fixed-point-free translation or a reflection
> `i ↦ k − i`; the transposition `(0 1)` is neither.  So any derivation must use
> at least one of `θ, ζ, π, ωₘ`, the operations that are not induced by
> bijections.

### Verdict on C1

**Open, and not worth another round.**  C2 makes it unnecessary: if `τ` is off
the critical path, its derivability is a question about Higman's operation list,
not about our chain.

---

## Bottom line, and what I recommend

1. **Take the C2 route.**  Land the three `GeneratedValue` rewrites (`σ` for
   `τ` twice, `ρ σ ρ` then `θ` once) and restate `OperationClosures` without the
   `tau` field for our chain.  That is a few dozen lines and it removes a leaf
   that three separate impossibility theorems now say is expensive.
2. **Put the canonical-variable-order requirement to the trace lane now**, while
   their design is still open.  It is the only thing that can bring `τ` back.
3. **Do not start route A.**  With `τ` off the critical path, the `d/e`
   apparatus buys our chain nothing, and the case for spending 2500–3500 lines
   on it disappears.  If Higman's theorem is ever wanted in full generality —
   all nine operations, for their own sake — the apparatus is still the only
   route, and `Seq.WindowSwapper` is the shape to aim at.
