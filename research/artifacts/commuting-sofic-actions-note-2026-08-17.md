# A negative answer to the commuting-sofic-actions question

2026-08-17. Self-contained note, written for external circulation; the
canonical statements live in the graph as
`commuting-sofic-actions-need-not-combine`,
`nonsofic-orbit-forces-commuting-counterexample` and
`gkp-sofic-action-toolkit`.

**Status.** Complete proof from two external inputs, one refereed (GKP) and
one an unrefereed preprint eleven days old (Kun–Thom). The group-theoretic
core of §3 — freeness of both coordinate actions, their commutation, and the
diagonal orbit being `G/H` with stabilizer `H` — is machine-checked in
`GroupApproximation/Algebra/DiagonalCosetAction.lean` (2026-08-18); the
soficity transfers are not formalized. A priority search on the date above
found no prior resolution; external confirmation from the authors is
outstanding. See the closing section.

---

## 1. The question

Gao, Kunnawalkam Elayavalli and Patchell, *Soficity for group actions on sets
and applications*, arXiv:2401.04945v3, *Res. Math. Sci.* **12** (2025), 48,
Section 4:

> **Question 4.2.** Suppose we have actions `α_i : G_i ↷ X` which commute with
> each other and where `i` ranges over a countable index set. Then the actions
> naturally give rise to an action `α : ⊕_i G_i ↷ X`. `α` is sofic iff all
> `α_i` are sofic?

They note that the forward direction follows from item 3 of their Proposition
2.15, and that by item 4 of the same proposition it suffices to consider two
groups.

The answer is **no**, already for two copies of one group, with both
coordinate actions free and the combined action transitive.

## 2. The inputs

All actions are of countable discrete groups on countable discrete sets, and
"sofic action" is Definition 2.1(5) of the cited paper. From that paper:

- **Theorem 2.14.** `G` sofic, `N ≤ G` locally finite ⟹ `G ↷ G/N` is sofic.
- **Proposition 2.15(2).** `α : G ↷ X` sofic ⟹ its restriction to each orbit
  is sofic.
- **Proposition 2.15(3).** `α : G ↷ X` sofic, `H ≤ G` ⟹ `α|_H` is sofic.
- **Proposition 2.16.** If the restriction of `α` to each of its orbits is
  sofic, then `α` is sofic.

Two immediate consequences. Taking `N = {1}` in Theorem 2.14, the regular
action of a sofic group is sofic; combined with Proposition 2.16, **every free
action of a sofic group on a countable set is sofic** (each orbit is
`G`-isomorphic to `G/{1}`, and soficity depends only on the isomorphism class
of the `G`-set — visible in their Proposition 2.9(2), where a `G`-equivariant
bijection transports `π` and leaves `φ` untouched). And by 2.15(2) with 2.16,
soficity of an action is exactly soficity of each of its orbits, so a nonsofic
action always contains a nonsofic transitive one.

From Kun and Thom, *Nonsofic wreath products of residually finite groups*,
arXiv:2608.06222v1 (6 August 2026): an explicit **residually finite, hence
sofic** group `G` with a subgroup `Γ` for which the coset action `G ↷ G/Γ` is
**not** sofic. Concretely, `Γ = EL_r(R_+)` and `G = EL_r(R) ⋊ SL_d(Z)` for a
prime power `q`, `r, d ≥ 3`, `R_+ = F_q[x_1,…,x_d]`,
`R = F_q[x_1^{±1},…,x_d^{±1}]` and `SL_d(Z)` acting by monomial substitutions
(their Theorem E); nonsoficity of the coset action follows from their Theorem
A together with GKP Theorem 3.6, and independently in the measure-theoretic
sense from their Corollary D.

## 3. Theorem

> Let `G` be a countable sofic group and `H ≤ G` a subgroup such that
> `G ↷ G/H` is not sofic. Then there is a countable set `X` with two commuting
> actions `α_1, α_2 : G ↷ X`, both free and both sofic, whose combined action
> `α : G × G ↷ X` is not sofic.

**Proof.** Let `ΔH = {(h,h) : h ∈ H} ≤ G × G` and `X = (G × G)/ΔH`, a
countable set, with `G × G` acting by left multiplication. Restricting to the
coordinate subgroups `G × {1}` and `{1} × G` gives

```text
α_1(g)·(a,b)ΔH = (ga, b)ΔH,       α_2(g)·(a,b)ΔH = (a, gb)ΔH,
```

two commuting actions of `G` whose combination is the left `G × G`-action.

*Both are free.* If `α_1(g)·(a,b)ΔH = (a,b)ΔH` then
`(a,b)^{-1}(g,1)(a,b) ∈ ΔH`. Conjugation in a direct product is
coordinatewise, so this element is `(a^{-1}ga, 1)`; equality with some `(h,h)`
forces `h = 1`, hence `a^{-1}ga = 1`, hence `g = 1`. Symmetrically for `α_2`.

*Both are sofic.* Free actions of a sofic group on a countable set are sofic,
by Theorem 2.14 with `N = {1}` and Proposition 2.16.

*The combination is not.* Let `ΔG = {(g,g) : g ∈ G}` and `x_0 = ΔH ∈ X`. The
map

```text
Φ : G/H → X,     Φ(gH) = (g,g)ΔH
```

is well defined (`(gh,gh)ΔH = (g,g)(h,h)ΔH = (g,g)ΔH`), injective
(`(g,g)ΔH = (g',g')ΔH` gives `(g^{-1}g', g^{-1}g') ∈ ΔH`, so `g^{-1}g' ∈ H`),
onto the `ΔG`-orbit `𝒪` of `x_0` by construction, and equivariant
(`Φ(kgH) = (k,k)·Φ(gH)`). Equivalently, the stabilizer of `x_0` in `ΔG ≅ G` is
exactly `H`.

Now suppose `α : G × G ↷ X` were sofic. By Proposition 2.15(3) its restriction
to the subgroup `ΔG` is sofic; by Proposition 2.15(2) the further restriction
to the orbit `𝒪` is sofic; and by `Φ` that action is isomorphic to
`G ↷ G/H`, which is therefore sofic — contradicting the hypothesis. `□`

## 4. Corollary

Applying the theorem to the Kun–Thom pair with `H = Γ`: on the countable set
`X = (G × G)/ΔΓ`, the actions

```text
g ·_1 (a,b)ΔΓ = (ga, b)ΔΓ,       g ·_2 (a,b)ΔΓ = (a, gb)ΔΓ
```

are commuting free sofic actions of `G` whose combined `G × G`-action is not
sofic. **Question 4.2 has a negative answer.**

Three features of the counterexample close off the obvious weakenings: the
combined action is transitive, both coordinate actions are free, and the two
acting groups are the same sofic group.

## 5. Remarks

**The construction is the authors' own, one subgroup further along.** On p. 15
of the same paper, GKP show that a positive answer to Question 4.2 would make
the conjugation action of every sofic group `Γ` on itself sofic: left and
right multiplication on `Γ` commute, both are sofic by Theorem 2.14, and
restricting the combined `Γ ⊕ Γ`-action along the diagonal gives conjugation.
That is precisely the construction above with `H = G`, where
`(G × G)/ΔG ≅ G` and the diagonal orbit of the base point degenerates to a
point. Replacing `ΔG` by `ΔH` turns the diagonal orbit into `G/H`, and the
question becomes a statement about coset actions rather than conjugacy
classes.

**What was actually missing was an example.** The same paper says, on p. 8:
*"It is still open whether all actions by sofic groups are sofic."* No
nonsofic action of a sofic group was known when the question was posed. Kun
and Thom produced one in August 2026, and Question 4.2 became answerable that
day. So the correct reading of this note is that the question was resting on
the existence problem for nonsofic actions, and fell with it.

**Only the transitive case is needed, and it comes for free.** By Proposition
2.15(2) with Proposition 2.16, any nonsofic action of a sofic group contains a
nonsofic orbit, which is a coset action. So the hypothesis of the theorem is
equivalent to "`G` is sofic and admits some nonsofic action".

**Scope.** This says nothing about Question 4.3 (free products in place of
direct sums), nothing about the conjugation action of a sofic group on itself
— the `H = G` degenerate case, where the implication proved by GKP runs the
other way — and nothing about Question 4.4 beyond what those already imply.

## 6. Priority and trust

The searches run on 2026-08-17 covered the question text, "commuting sofic
actions", the construction itself, citations of the GKP paper, and work
following Kun–Thom, and found no prior resolution. Alekseev–Bradford
(arXiv:2601.18742), the other systematic treatment of sofic actions, states no
permanence result for commuting actions and does not mention Question 4.2.
This is a priority search, not a guarantee: the step from `ΔG` to `ΔH` is
small enough that an author could have made it privately.

The proof of the theorem in §3 depends only on the refereed GKP paper. The
corollary in §4 additionally depends on Kun–Thom arXiv:2608.06222v1, which is
unrefereed; if their Theorem A or Theorem E fails, §4 fails and §3 stands.

Suggested next step: send §§1–4 to Gao, Kunnawalkam Elayavalli, Patchell, Kun
and Thom before any priority is claimed in print.
