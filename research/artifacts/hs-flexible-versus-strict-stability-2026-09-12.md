# Flexible versus strict Hilbert–Schmidt stability: sources and the amenable coincidence

Lane `hs-flexible-not-strict-example`, 2026-09-12. This document records the
sources read from the PDFs and the lane's result. The graph nodes are:

- `injective-limit-trace-flexible-hs-repair-is-strict` and its `-proof` route;
- `amenable-flexible-hs-stability-is-strict-hs-stability` and its `-proof`
  route;
- the open claim `flexibly-but-not-strictly-hs-stable-group-exists`.

## 1. Sources read from the PDFs

**Dogon, arXiv:2211.10492v3 (25 Aug 2023), pp. 2–4.**
- **Definition 1.2** (Becker–Lubotzky, cf. Ioana): `φ_n : Γ -> U(d_n)` is an
  asymptotic homomorphism if `lim_n ||φ_n(g)φ_n(h) - φ_n(gh)||_2 = 0` for all
  `g,h`. "The group Γ is said to be flexibly HS-stable if for every asymptotic
  homomorphism φ_n : Γ -> U(d_n) there exists a sequence of true homomorphisms
  π_n : Γ -> U(D_n) for some D_n ≥ d_n with lim D_n/d_n = 1 such that
  lim_n ||φ_n(g) - P_n π_n(g) P_n||_2 = 0 for all g ∈ Γ, where P_n is the
  projection onto the first d_n-coordinates."
- **Footnote 1:** "A group Γ is HS-stable if it satisfies definition 1.2 with
  D_n = d_n for all n."
- **p. 3:** "Many amenable groups have been shown to be (flexibly) HS-stable,
  including all finitely generated virtually nilpotent groups, certain
  lamplighter groups and the Baumslag-Solitar groups BS(1,n) [40].
  Non-amenable examples include certain one-relator groups (Theorem 8 in [27])
  and virtually free groups [22]. One can obtain further examples by taking
  direct products with HS-stable amenable groups [29]."
- **p. 3:** "On the other hand, any finitely generated hyperlinear group that
  is not residually finite cannot be flexibly HS-stable [7]. Ioana, Spaas and
  Wiersma [28] showed that SL_2(Z) ⋉ Z^2 is not flexibly HS-stable, giving the
  first residually finite example. For groups of very different nature, Ioana
  [31] proved that F_m × F_k is not flexibly HS-stable, F_m, F_k being
  non-abelian free groups."
- **p. 3:** "Flexible HS-stability was defined by Becker and Lubotzky [7] after
  they proved that infinite hyperlinear property (T) groups are never
  HS-stable, in hopes that some might be flexibly HS-stable. ... Thus, deciding
  flexible HS-stability in this scenario is extremely interesting. With that
  said, there is no known example of a group that is flexibly HS-stable, but
  not HS-stable."
- **p. 4:** "Weak ucp-stability is a strictly weaker property when compared
  with flexible HS-stability: indeed, by Corollary 1.7 in [28] any group Γ such
  that C*(Γ) possesses Kirchberg's local lifting property (LLP) is weakly
  ucp-stable. Thus, by the Choi-Effros lifting theorem [14], any amenable group
  is weakly ucp-stable. Yet, an amenable group which is not residually finite
  cannot be flexibly HS-stable (see [7])."

**Hadwin–Shulman, arXiv:1706.08405v3 (25 Mar 2019), pp. 2–12.**
- **Definition 3:** stability means that homomorphisms into tracial
  ultraproducts lift.
- **Proposition 1:** "For a finitely presented group the two definitions of
  stability above coincide."
- **Theorem 1:** matricially stable groups are closed under finite free
  products and direct products with an abelian group.
- **Theorem 3:** "If G is matricially stable, then each embeddable character
  of G is a pointwise limit of traces of finite-dimensional representations."
- **p. 9:** "On an amenable group every character is embeddable."
- **Theorem 4:** "Let G be an amenable group. The following are equivalent:
  (1) G is matricially stable (2) G is W*-factor stable. (3) Each character of
  G is a pointwise limit of traces of finite-dimensional representations."
- **Proposition 3:** "Let G be a maximally almost periodic group. Then δ_e is
  a pointwise limit of traces of some finite-dimensional representations of G."

**Jung, arXiv:math/0506108v3 (2 Dec 2006), pp. 1–4.**
- **§1:** Γ(X;m,k,γ) is the set of n-tuples of selfadjoint k×k matrices with
  `|tr_k(a_(i1)...a_(ip)) - φ(x_(i1)...x_(ip))| < γ` for `1 ≤ p ≤ m`. No norm
  bound is imposed.
- **Lemma 2.9:** (1) M is amenable ⇔ (2) X is tubular, under the standing
  assumption that M embeds into R^ω.
- **Proof of Lemma 2.4:** tubularity is used for every k: "for any k ∈ N, if
  ξ, η ∈ Γ(F; m(p), k, m(p)^(-1)), then there exists a u ∈ U_k ...".

**Downloaded but not extracted.** Becker–Lubotzky arXiv:1809.00632,
Fournier-Facio–Gerasimova–Spaas arXiv:2307.13155 and Dogon–Vigdorovich
arXiv:2506.20843 are in `hsflex-lit/` on MSI. Two extraction attempts failed:
the poppler module is missing GLIBCXX, and a ghostscript run was stopped by
the MSI auth breaker. Nothing here depends on them beyond what main already
imports.

## 2. Result

**Theorem A (sequence level).** Let `Γ` be finitely generated, `α_n` an
asymptotic homomorphism, `ω` a nonprincipal ultrafilter, and
`τ = lim_ω tr α_n`. Suppose flexible repair holds along `ω` with
`lim_ω D_n/d_n = 1`, and `L_τ(Γ)` is injective. Then same-dimensional repair
holds along `ω`.

Proof outline:
1. **Trace transfer.** `|tr_D π(g) - tr_d α(g)| <= ||α(g) - PπP||_(2,d) + 2(1 - d/D)`.
2. **A convergent subsequence.** Some genuine `σ_k` have `tr σ_k -> τ`.
3. **Exact dimension.** Pad `σ_k(n)` with trivial summands to dimension
   exactly `d_n`, with `e_k(n)^2 <= d_n`. Bounded `d_n` is handled by
   compactness.
4. **Two embeddings.** Both ultraproduct homomorphisms give trace-preserving
   embeddings of `L_τ(Γ)`.
5. **Conjugation.** Jung tubularity conjugates the two `d_n`-dimensional
   microstates, generator by generator.
6. **Diagonalize.**

**Theorem B (group level).** If `Γ` is finitely generated and
`Γ/Rad_fd(Γ)` is amenable, flexible HS-stability equals HS-stability. The
limit trace of any flexibly repairable sequence is a limit of
finite-dimensional characters. So it is trivial on `Rad_fd(Γ)`, the GNS
representation factors through the amenable quotient, and `L_τ(Γ)` is
injective: the commutant of a representation of an amenable group is
injective, hence so is the generated algebra.

**Consequences.**
- The amenable dimension-parity route to a separating group is closed.
  Trivial summands absorb parity, and tubularity removes the conjugacy
  obstruction.
- A hyperlinear separating group is residually finite and non-amenable.
- Any separating sequence has non-injective limit traces. That includes the
  explicit `PSL_2(Z[1/2])` sequence of
  `sl2-half-explicit-strict-flexible-separation`.

## 3. Map of regimes for a separating group

| regime | status |
| --- | --- |
| amenable, or amenable maximal almost periodic quotient | no separation (Theorem B) |
| hyperlinear, not residually finite | not flexibly stable (Dogon p. 3, [7]) |
| `SL_2(Z) ⋉ Z^2`, `F_m × F_k` | not flexibly stable (Dogon p. 3, [28], [31]) |
| virtually nilpotent, `BS(1,n)`, some lamplighters, some one-relator, virtually free, products with HS-stable amenable, free products of matricially stable | listed as (flexibly) HS-stable; no known separation |
| infinite hyperlinear Kazhdan groups | strict fails; flexible = weak ucp (main); for `Sp_2g(Z)` flexible stability yields a non-hyperlinear group |
| `PSL_2(Z[1/2])` | strict fails (explicit Weil sequence); flexible stability yields a non-hyperlinear finite central extension (Dogon–Vigdorovich Cor. 1.5 on main) |
| `SL_n(Z)`, `n >= 3` | strict fails (Kazhdan); flexible is Becker–Lubotzky's open question |
| LLP + property FD (Fournier-Facio–Willett) | very flexible, with no ratio condition; a ratio-one upgrade plus a strict obstruction on a non-injective trace would give an example; not attempted |

No famous question is settled here. The lane proves the coincidence theorem
above and narrows where Dogon's separation can live.
