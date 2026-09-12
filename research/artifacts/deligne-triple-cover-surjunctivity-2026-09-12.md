# Deligne's triple cover: surjunctivity structure (lane w3-deligne, 2026-09-12)

Target: `finite-normal-subgroups-do-not-affect-surjunctivity`, whose open residue is finite normal
subgroups inside the finite residual. The first test instance is Deligne's connected triple cover

```text
1 -> C_3 = <z> -> E_3 -> Gamma = Sp_4(Z) -> 1,
```

with `Res_fin(E_3) = C_3` (`deligne-triple-cover-finite-residual-is-center`). Nothing in this artifact
decides whether `E_3` is surjunctive.

## 0. What main records about E_3 before this artifact

- `Res_fin(E_3) = C_3`, so the separated case (`separated-finite-normal-subgroups-preserve-surjunctivity`)
  never applies to `C_3 <= E_3`.
- `E_3` is finitely presented (`fg-central-extension-of-fp-group-is-fp`). For finitely presented groups,
  LEF is the same as residual finiteness, so `E_3` is not LEF.
- MF radical: `deligne-triple-cover-is-not-mf` and `deligne-triple-cover-exact-mf-radical` are recorded
  on main.
- Hyperlinearity of `E_3` is open, with exact reformulations
  (`deligne-sector-gap-is-exactly-nonhyperlinearity`, `nonhyperlinear-via-deligne-central-mark-collapse`).
- No claim on main records soficity or surjunctivity of `E_3`.
- The sofic radical of `E_3` lies in `Res_fin(E_3) = C_3`, because finite quotients are sofic. It is `1`
  or `C_3`. So `E_3` is sofic exactly when some homomorphism into a sofic group keeps `z != 1`
  (residually sofic groups are sofic).

## 1. Modular stable finiteness across finite normal p-subgroups

Throughout, `k` is a field of characteristic `p`, `N` is a finite normal subgroup of a group `E`,
`pi : k[E] -> k[E/N]` is the quotient map, `J = ker pi`, and `omega` is the augmentation ideal of `k[N]`.

**Lemma 1.1 (augmentation kernel).** `J = k[E] omega = omega k[E]`, and `J^m = omega^m k[E]` for every
`m >= 1`.

*Proof.* Choose a transversal `T` with `E = disjoint union of t N` over `t in T`. Every `x in k[E]` is
uniquely `sum_t t a_t` with `a_t in k[N]`, and `pi(x) = sum_t eps(a_t) tN`, where `eps` is the
augmentation of `k[N]`. Distinct `t` give distinct cosets, so `x in J` iff every `a_t in omega`. Hence
`J = sum_t t omega = k[E] omega`. Conjugation by `g in E` permutes `N`, so `g omega g^(-1) = omega`, hence
`k[E] omega = omega k[E]`. Then `J^(j+1) = omega^j k[E] omega k[E] = omega^j omega k[E] k[E] = omega^(j+1) k[E]`.

**Lemma 1.2 (nilpotent augmentation).** If `N` is a `p`-group, then `omega^|N| = 0`.

*Proof.* Induction on `|N|`; the case `|N| = 1` is trivial. Otherwise pick a central `c in N` of order `p`
and put `u = c - 1`. It is central in `k[N]` and `u^p = c^p - 1 = 0`, since the binomial expansion of
commuting elements has vanishing middle coefficients in characteristic `p`. By Lemma 1.1 applied to
`<c> <= N`, and `c^j - 1 = u (1 + c + ... + c^(j-1))`, the kernel of `k[N] -> k[N/<c>]` is `I = u k[N]`,
with `I^p = u^p k[N] = 0`. The augmentation ideal of `k[N/<c>]` satisfies `omega'^(|N|/p) = 0` by
induction, so `omega^(|N|/p) <= I` and `omega^|N| <= I^p = 0`.

**Lemma 1.3 (stable finiteness across nilpotent ideals).** Let `R` be a ring and `I` a two-sided ideal
with `I^m = 0`. Then `R` is stably finite iff `R/I` is.

*Proof.* `M_n(I)` is a two-sided ideal of `M_n(R)` with `M_n(I)^m = 0` and `M_n(R)/M_n(I) = M_n(R/I)`, so
it suffices to compare direct finiteness of `R` and `R/I`.
- If `R/I` is directly finite and `ab = 1` in `R`, then `e = ba` is idempotent with image `1`, so `1 - e`
  is an idempotent in `I`, hence `1 - e = (1 - e)^m = 0`.
- If `R` is directly finite and `abar bbar = 1` in `R/I`, lift to `a, b`. Then `ab = 1 + i` with `i in I`,
  a unit with inverse `sum_(j<m) (-i)^j`. With `b' = b (ab)^(-1)` we get `ab' = 1`, so `b'a = 1`. Since
  `(ab)^(-1)` maps to `1`, `b'` maps to `bbar`, so `bbar abar = 1`.

**Theorem 1.4** (`finite-normal-p-subgroups-preserve-modular-stable-finiteness`). If `N` is a finite normal
`p`-subgroup of `E` and `char k = p`, then `k[E]` is stably finite iff `k[E/N]` is.

*Proof.* By Lemmas 1.1 and 1.2, `J` is a two-sided ideal with `J^|N| = 0`, and `k[E]/J = k[E/N]`. Apply
Lemma 1.3.

No residual finiteness is used, so the theorem applies inside the finite residual.

**Remark 1.5 (linear automata).** Take `k` finite. By `certificate-linear-automata-have-local-linear-decoders`
with a one-letter certificate alphabet, an injective `k`-linear automaton `T` on `(k^n)^E` has a linear
left inverse `S`. Linear automata over `E` compose like matrices over `k[E]` or over its opposite ring,
and `g -> g^(-1)` identifies `k[E]` with its opposite, so direct finiteness is unaffected. A strict `T`
gives `ST = id != TS`, so `M_n(k[E])` is not directly finite. Hence: if `N` is a finite normal `p`-subgroup
and `k[E/N]` is stably finite, then `E` carries no strict `k`-linear automaton in characteristic `p`.

**Remark 1.6 (instances).**
- `E_3` at `p = 3`: Section 2.
- The Clifford cover `E_S`, central `Z/2` over a Kun–Thom wreath `W` (lane w3-free-neg, dcbd89f07a): at
  `p = 2`, the one characteristic where its character splitting is unavailable, Theorem 1.4 gives that
  `k[E_S]` is stably finite iff `k[W]` is (`kun-thom-wreath-stably-finite`).
- For `p` not dividing `|N|` the kernel `J` is not nilpotent, and the algebra splits over characters
  instead (Section 4).

## 2. Deligne's triple cover in characteristic three

**Theorem 2.1** (`deligne-triple-cover-ternary-group-algebras-are-stably-finite`). For every field `k` of
characteristic `3`, `k[E_3]` is stably finite.

*Proof.* `Gamma = Sp_4(Z)` is a finitely generated linear group, hence residually finite
(`finitely-generated-linear-groups-are-residually-finite`). A residually finite group is LEF: any finite
subset maps injectively into a finite quotient, and the quotient map preserves products. So `k[Gamma]` is
stably finite (`lef-group-rings-over-stably-finite-rings-are-stably-finite`, with the coefficient ring
`k`). The center `C_3` is a normal `3`-subgroup with `E_3/C_3 = Gamma`, and Theorem 1.4 applies.

**Corollary 2.2 (screens on strict automata over E_3 in characteristic three).**
- **(a) Linear.** No strict `k`-linear automaton on `(k^n)^(E_3)` exists for finite `k` of characteristic
  `3` (Remark 1.5).
- **(b) Formal.** Over an alphabet `F_3^n`, no strict pair `(tau, sigma)` on `E_3` has polynomial
  representatives with `sigma o tau = id` holding formally, by
  `formal-polynomial-strict-pairs-need-unstable-linearization` with `M_n(F_3[E_3])` directly finite.
- **(c) Low degree.** Over `F_q^m` with `q` a power of `3`, every strict pair on `E_3` has
  `deg sigma * deg tau >= q` after translating so that `tau(0) = 0`, by
  `low-degree-strict-automata-force-matrix-kaplansky-failure`.
- **(d) Conditional.** If `prime-field-left-inverse-pairs-are-stably-formalizable` holds at `p = 3`, then
  `E_3` is surjunctive over every alphabet of size `3^n`: a strict pair would become formalizable after
  adding identity tracks, against (b) at size `n + k`.

**Remark 2.3 (what survives in characteristic three).** A strict automaton on `E_3` over a `3`-power
alphabet must be non-formalizable at every stabilization, so its left-inverse identity genuinely uses
`x^q = x`. No such pair is known on any group.

## 3. Memory groups of strict automata over finite normal extensions

**Lemma 3.1 (coset restriction).** Let `tau` on `A^E` have memory `M <= H <= E`. Then `tau` is injective,
respectively surjective, iff its restriction `tau_H` on `A^H` is.

*Proof.* `tau(x)(g) = mu((x(gm))_(m in M))`, and `g, gm` lie in the same left coset `gH`. With a transversal
`T` of `E/H`, `A^E = prod_(t in T) A^(tH)`, identify `A^(tH)` with `A^H` by `h -> x(th)`. Then `tau` acts
as `tau_H` on each factor, and a product map is injective or surjective iff each factor is.

**Theorem 3.2** (`strict-automata-memory-keeps-finite-normal-kernel-residual`). Let `N` be a finite normal
subgroup of `E` with `E/N` surjunctive, `tau` a strict automaton on `A^E` with memory set `M`, and
`H = <M>`. Then:
- `tau_H` is strict over `H`;
- `H cap N` injects into no finite quotient of `H`, equivalently `N cap Res_fin(H) != 1`;
- `H` is not sofic.

*Proof.*
1. Lemma 3.1 gives the first item.
2. Suppose `H cap N` injects into a finite quotient of `H`. By
   `separated-finite-normal-subgroups-preserve-surjunctivity`, `H` is surjunctive iff
   `H/(H cap N) = HN/N` is. That group lies in `E/N`, so it is surjunctive by
   `surjunctivity-passes-to-subgroups`. Then `tau_H` could not be strict.
3. **Equivalence.** If `N cap Res_fin(H) = 1`, each `x in (H cap N) \ 1` lies outside some finite-index
   normal `K_x <= H`. As `N` is finite, `K = intersection of the K_x` has finite index and
   `K cap N = 1`, so `H cap N` injects into `H/K`. Conversely, an injection into `H/K` gives
   `Res_fin(H) cap N <= K cap N = 1`.
4. A sofic `H` would be surjunctive (`sofic-groups-are-surjunctive`).

**Corollary 3.3 (E_3).** The memory group `H` of any strict automaton on `E_3` contains `z`, has
`z in Res_fin(H)`, and is nonsofic. So `Lambda = H/<z>` is a finitely generated subgroup of `Sp_4(Z)` over
which the triple cover does not virtually split. Two classes of `Lambda` are excluded:
- **Virtually free `Lambda`.** For a free finite-index `F <= Lambda`, the central extension of `F` by `C_3`
  splits. A splitting subgroup `F'` has finite index in `H` and meets `C_3` trivially.
- **Amenable `Lambda`.** Then `H` is amenable, hence sofic.

This includes the block `SL_2(Z) <= Sp_4(Z)`, which is virtually free.

**Remark 3.4 (fixed configurations).** `z` is central, so right translation by `z` commutes with `tau`.
By `surjectivity-descends-to-centralized-coset-quotients`, `tau` acts on `z`-invariant configurations as an
injective automaton over `Gamma`. `Gamma` is residually finite, hence surjunctive, so that restriction is
bijective. Every configuration missed by a strict `tau` therefore has trivial `C_3`-stabilizer.
