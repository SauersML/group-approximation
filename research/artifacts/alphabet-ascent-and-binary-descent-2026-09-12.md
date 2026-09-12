# Alphabet ascent and binary descent of strictness

Lane w3-alphabet. Two alphabet bridges for Gottschalk's conjecture: ascent (strict rules over `k`
symbols give strict rules over every `n >= k`) and descent (a group carrying a strict automaton over
some alphabet carries one over two symbols). Neither is decided. This records a positive ascent
mechanism covering every classified strict table, the reduction of general ascent to that mechanism,
and a precise reformulation of descent with its obstruction.

## 1. Ascent: passive-block involution codes (positive)

See `passive-block-involution-codes-ascend` and its proof route.

A **control-involution code** over `A` has `mu = nu` and relay rule `mu(x) = g_{x(c_2)}(x(c_1))` for a
data cell `c_1` and a control cell `c_2`, where `v |-> g_v` sends `A` to involutions of `A`, `g_v`
depends only on a partition block of `v`. A block `Z` is **passive** when every `g_v` fixes `Z`
pointwise.

**Lemma.** A control-involution code strict for `(T_f, T_r)` over `A` with a nonempty passive block
extends, by adjoining a new symbol to the passive block and fixing it under every `g_v`, to a strict
code over `A ⊔ {∗}`. Hence the admissible sizes of `(T_f, T_r)` are upward closed above the first size
carrying such a code.

The decoder identity is a conjunction of equations "(word in the `g`'s)(demanded symbol) = demanded
symbol"; a symbol fixed by every `g_v`, placed in a pointwise-fixed block, satisfies every such
equation (identity factors drop out, and the new symbol is a global fixed point), and the `T_r` witness
stays inside `A`. Full argument in the proof route.

**Coverage of the classified tables.**
- Copy-code tables (`O ~ X`, `O ~ B`, `O ~ A`) are not involution codes but are defined over every
  `n >= 2` directly.
- `x_a = x_b` (`B ~ A`): `g_P = id` on `P = {0,1}`, `g_Q = (0\,1)` on `Q = A \ P`. `Q` is passive.
  Threshold `n = 3`, ascends to all `n >= 3`.
- `x_a = x_b = x_a x_b` (`B ~ A ~ X`): `h_0 = id`, `h_1 = (0\,2)`, `h_2 = (0\,1)`, `h_w = id` for
  `w >= 3`. Passive block `{3,4,...}`, nonempty from `n = 4`; `n = 3` is the separate base.

So all three admissible-size patterns recorded in the Boolean-core artifact (Section 6) come from this
one mechanism, rather than from three separate computations.

## 2. General ascent reduces to this form

`strict-rule-pairs-ascend-to-larger-alphabets` asks for ascent of an arbitrary strict rule pair. Section
1 gives ascent whenever the pair is a copy code or a control-involution code with a passive block. So:

**Reduction.** General ascent holds if every strict rule pair is equivalent, over its alphabet and for
its tables, to a copy code or to a control-involution code with a passive block.

Two cautions on trying to prove the reduction.
- **The obstruction to naive extension is real.** Adjoining an *absorbing* symbol (`∗` swallows every
  relay that reads it) breaks the decoder identity exactly as the erasure symbol does (Boolean artifact,
  Section 5): a demanded `A`-symbol adjacent to a `∗` is lost. The passive-block mechanism works only
  because `∗` is a *fixed point* of involutions, not a sink. A general strict pair has no canonical
  fixed-point extension, which is why the general statement is open.
- **Monotonicity is not automatic.** Solvability of a single-demand network code need not be monotone in
  alphabet size in general; whether the uniform-relay, transpose-failing restriction here forbids
  non-monotone behaviour is exactly the open question. This is a heuristic pointer, not a cited theorem;
  no source was checked.

## 3. Descent to two symbols: reformulation and obstruction

`surjunctivity-failure-descends-to-binary-alphabet`: if `K` is not `A`-surjunctive it is not
`{0,1}`-surjunctive, with memories and tables allowed to change.

**Reformulation.** `K` is not `{0,1}`-surjunctive iff there is an injective non-surjective continuous
shift-equivariant map `{0,1}^K -> {0,1}^K`. A sufficient route from a strict automaton `tau` on `A^K`:
an equivariant continuous injection `e : A^K -> {0,1}^K` with an equivariant continuous retraction
`r` (`r o e = id`) whose image is clopen; then `e o tau o r` together with the identity off `e(A^K)`
is a strict automaton on `{0,1}^K`. So descent reduces to an equivariant **binary coding** of `A^K`
with a one-sided inverse, plus strictness transfer.

**Obstruction (block coding).** The only known binary coding is block coding over a finite subgroup
`H <= K` with `2^{|H|} >= |A|`: fix an injection `A ↪ {0,1}^H` and read each coset `gH` as one
`A`-symbol. Decoding `x |-> (d((x(gh))_{h in H}))_g` is equivariant. Encoding needs an equivariant
choice of how to lay the `|H|` bits inside each coset `gH`, i.e. an equivariant marking of `K/H`.

- A `K`-equivariant transversal marker of `K/H` is a coloring/SFT datum a group need not admit.
- On a finitely generated infinite simple group — the hosts Gottschalk reduces to — there is no proper
  finite-index subgroup and no nontrivial finite quotient, and a finite subgroup `H` has infinite-index
  normalizer, so no equivariant marking of `K/H` is available. Block-code descent is therefore
  unavailable on exactly the hosts the conjecture needs.

So any descent proof for the target hosts must produce a markerless equivariant binary coding. None is
known. (The marker discussion is a structural sketch, not a fully formalized theorem.)

**What is settled against descent at the fixed-table level.** Descent cannot be proved by holding tables
fixed: `equal-label-table-is-strict-at-three-symbols-not-two` gives a table strict over every `n >= 3`
and over no `n = 2`. Any group-level descent must enlarge memories.
