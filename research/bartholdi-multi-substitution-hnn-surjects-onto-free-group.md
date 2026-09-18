---
rg: 2
id: bartholdi-multi-substitution-hnn-surjects-onto-free-group
kind: claim
title: The finitely presented group built from an ascending L-presentation with k ≥ 2 substitutions surjects onto the free group of rank k, so the amenability clause of Bartholdi's Theorem thm:hnn needs a single substitution
distinct_from:
  grigorchuk-supergroup-fp-amenable-hnn-satisfies-boone-higman: that uses Bartholdi's theorem with one substitution, where the amenability clause is correct; this records that the clause fails with two or more.
  fabrykowski-gupta-ascending-hnn-satisfies-boone-higman: that treats the one-letter extension Γ*_σ; this shows the three-letter finitely presented group from Bartholdi's printed presentation of Γ is not amenable.
---

**ESTABLISHED** (elementary; checked by hand on generators). Honest status: this is a gap in
the statement as printed in arXiv:math/0007062v3, not in any of the paper's named
applications. The published version (J. Algebra 268, 2003) was not checked, and may have
the restriction. The author was not contacted.

## Source (arXiv:math/0007062v3, TeX `lpres.tex`, read at `$GQ/src/bh-free-20/bart/`)

- **Definition (l.119–136).** An L-presentation is `⟨S | Q | Φ | R⟩`, with `Φ` "a set of free
  group homomorphisms". It is "finite if S, Q, Φ, R are finite. It is ascending if Q is
  empty." Nothing restricts `|Φ|`.
- **Theorem `thm:hnn` (l.340–348).** "Let G be finitely L-presented by an ascending
  L-presentation. Then a finitely presented group Ĝ containing G can be effectively
  constructed. Moreover, Ĝ is an ascending HNN extension of G by a finite number of stable
  letters. In case G is amenable, Ĝ is a finitely presented amenable group containing G."
- **Proof (l.349–357).** "Let ⟨S ‖ Φ⟩R be a finite ascending L-presentation of G. Consider
  the group Ĝ = ⟨S ∪ Φ | R ∪ {s^φ = φ(s)}_{s∈S, φ∈Φ}⟩."

## Statement

For any finite ascending L-presentation with `|Φ| = k`, the assignment

```text
π(s) = 1   (s ∈ S),        π(φ) = x_φ   (φ ∈ Φ)
```

defines a surjection `π: Ĝ → F(x_φ : φ ∈ Φ) ≅ F_k`:
- each `r ∈ R` is a word in `S`, so `π(r) = 1`;
- for `s^φ = φ(s)`: the left side maps to `x_φ^{-1}·1·x_φ = 1`, and the right side, a word in
  `S`, maps to `1`.

For `k ≥ 2`, `F_k` is not amenable, and amenability passes to quotients. So **`Ĝ` is not
amenable**, whatever `G` is.

For `k = 1`, `Ĝ = G*_φ` is an ascending HNN extension, which is amenable when `G` is. So the
clause is correct there.

## Hand check on the printed Fabrykowski–Gupta presentation (Theorem `thm:Gamma`)

Here `S = {a, r}` and `Φ = {σ, χ_1, χ_2}`. `R` consists of `a³` and two iterated relators,
all words in `a, r`. The substitutions are:
- `σ: a ↦ r^{a^{-1}}, r ↦ r`;
- `χ_1: a ↦ a, r ↦ r^{-1}`;
- `χ_2: a ↦ a^{-1}, r ↦ r`.

So `Ĝ_Γ = ⟨a, r, σ, χ_1, χ_2 | R, a^σ = r^{a^{-1}}, r^σ = r, a^{χ_1} = a, r^{χ_1} = r^{-1},
a^{χ_2} = a^{-1}, r^{χ_2} = r⟩`. Under `π` (`a, r ↦ 1`; `σ, χ_1, χ_2 ↦ x_1, x_2, x_3`):
- the relators in `R` map to `1`;
- each of the six conjugation relations maps to `1 = 1`.

So `Ĝ_Γ ↠ F_3`, and `Ĝ_Γ` is not amenable. It is finitely presented and contains `Γ`.

## Which uses are affected

- **Unaffected (one substitution).** The first Grigorchuk group (Lysenok's `σ`), the
  Grigorchuk supergroup (`σ̃`), Brunner–Sidki–Vieira (`φ`), and Basilica (Bartholdi–Virág).
- **Affected.** The Fabrykowski–Gupta group (`σ, χ_1, χ_2`). Whether `Γ*_σ` alone is finitely
  presented is not settled here. It would follow from a σ-only ascending presentation, which
  the paper mentions in its proof ("from 6 iterated relators to 2") but does not display.
- **Not applicable.** For the Gupta–Sidki group, `Q ≠ ∅`, so the presentation is not
  ascending.

## Lesson for general BH

Finite presentation is cheap for L-presented groups, but each extra substitution adds a free
stable letter. So "fp overgroup" and "amenable fp overgroup" separate as soon as `|Φ| ≥ 2`. BH
does not care about amenability: the multi-letter group `Ĝ` is a graph of groups with one
vertex and `k` ascending loops. So the natural BH question is closure of the one-point
germ-extension hosts under several ascending HNN letters at once. That is the closure question
taken up next (`f-infinity-tail-ascending-hnns-satisfy-boone-higman`).
