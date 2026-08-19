# Glebsky's weak-soficity permanence: where the metric freedom is, and what it costs

Date: 2026-08-14

## 0. Summary

Two papers, both read in full from the PDF on 2026-08-14:

* **[G19]** L. Glebsky, *Extension of a residually finite group by a residually
  finite group is weakly sofic*, arXiv:1910.08631v1, 6 pp.  Theorem 1: `H ⊴ K`,
  `H` and `G = K/H` residually finite `⟹ K` weakly sofic.  (Published as
  Rev. Mat. Iberoam. 39 (2023) 1097–1104 with `H` weakly sofic; the v1 form
  already covers the Kun--Thom wreath, whose kernel is residually finite.)
* **[G17]** L. Glebsky, *Approximation of groups, characterizations of sofic
  groups, and equations over groups*, arXiv:1506.06940 = J. Algebra 477 (2017)
  147–162.

**Finding 1.  [G19] contains no metric surgery.  It contains no metric.**
Nowhere in the six pages is a bi-invariant length function constructed, chosen,
rescaled or even mentioned after the introduction.  The proof is entirely
profinite and equational.  The expectation that the proof "manufactures a metric
adapted to the extension" is false; the metric freedom is spent one level down,
in [G17].

**Finding 2.  The metric freedom is exactly Lemma 3 of [G17]**, which
manufactures an invariant length on a finite group out of a purely algebraic
separation condition, using the Cayley graph of a conjugation-closed generating
set.  This is the unique type-(b) step of the whole architecture.  Section 4
below extracts the resulting length in closed form; it is the object that must
be tested for Hilbert embeddability.

**Finding 3.  The architecture cannot be transported to `(U(n), ‖·‖₂)` verbatim,
and the failure is provable, not merely a gap.**  Corollary 19 of [G17] — the
characterization [G19] runs on — carries the hypothesis `K ⊆ Fin`; and even
granting a hyperlinear analogue of it, the universal-solution step (Lemma 4 of
[G19]) demands exact solvability of the relevant systems in a *finite* auxiliary
group, which the unitary system class provably does not give.  Section 5 gives
the counterexample `x² = a`.

**Finding 4.  The nearest counterexample is real but does not apply.**
De Chiffre--Glebsky--Lubotzky--Thom, arXiv:1711.10238 = Forum Math. Sigma 8
(2020) e18 — cited by Glebsky, and **beware the numbering: it is `[6]` in the
arXiv v1 bibliography (where the 2017 characterization paper is `[9]`) and
`[2]` in the published Rev. Mat. Iberoam. version (where the 2017 paper is
`[6]`).  Always name the paper, never the number.**  DGLT
which produces a **residually-finite-by-finite** group that is *not*
approximable by `U(n)`.  That is the Frobenius (unnormalized
Hilbert--Schmidt) norm, and DGLT say verbatim: *"Our techniques do not apply
directly to the context of (iii) [the normalized Hilbert--Schmidt norm], so we
cannot say anything conclusive about Connes' Embedding Problem."*  So the
naive metric analogue of Theorem 1 is **false for the Frobenius norm** and
**open for the normalized one**.  Glebsky's theorem is not metric-robust; the
class it holds for is not an arbitrary metric class.

## 1. The architecture of [G19]

```text
K residually-finite-by-residually-finite
  --(1) Kaluzhnin--Krasner--> K <= H wr G  (UNRESTRICTED: H^G semidirect G)
  --(2) residual reduction--> suffices: H finite, G f.g. residually finite
  --(3) [G17] Cor. 19------->  suffices: every w in Sys(Fin) solvable over H wr G
  --(4) Lemma 4------------->  an (H,a)-universal solution u in Ghat^n exists
  --(5) Sections 5,6-------->  locality + Tychonov limit give a solution in H wr Gamma,
                               Gamma = <G,u> <= Ghat
```

Note that step (1) produces the **unrestricted** wreath product `H^G ⋊ G`, not
`⊕_G H ⋊ G`.  This is why no existing wreath permanence theorem applies: for
`H` finite and `G` infinite, `H^G` is uncountable, and `H^G ⋊ G` is
*amenable-by-sofic*, which Elek--Szabó's sofic-by-amenable theorem does not
cover.  Soficity of `H^G ⋊ G` is exactly the open "is every
residually-finite-by-residually-finite extension sofic?" question that [G19]
§7 leaves open.

## 2. Step-by-step classification

Type **(a)** = works for any approximation class closed under subgroups and
residual limits; type **(b)** = uses the freedom to choose the metric, or the
finiteness of the class.

| step | content | type | fate under `(U(n), ‖·‖₂)` |
|---|---|---|---|
| (1) Kaluzhnin--Krasner | `K ↪ H ≀ G` unrestricted | (a) | survives: hyperlinearity passes to subgroups |
| (2) residual reduction | `H` RF `⟹ H ≀ G` residually `{H_i ≀ G}`, `H_i` finite; residually-𝒞 `⟹` 𝒞 | (a) | survives: approximability is a local property (Alekseev--Bradford Remark 3.3), so residually hyperlinear implies hyperlinear |
| (3) characterization | `K` weakly sofic `⟺` every `w̄ ∈ Sys(Fin)` solvable over `K` ([G17] Cor. 19) | **(b)** | **unavailable**: Cor. 19 assumes `K ⊆ Fin`, and its engine is [G17] Lemma 3 |
| (4) universal solution | `X_N ≠ ∅` because `D_N ⋊ G_N` is a **finite** group and `w̄ ∈ Sys(Fin)`; then inverse limit of nonempty **finite** sets | **(b)** | **provably fails**, see §5 |
| (5) locality (Lemma 5) | `ψ(x) = ψ̃(x_γ)` whenever `x·Suf(p)(ᾱ) ⊆ T_γ` | (a) | survives verbatim; purely combinatorial |
| (6) Tychonov limit (Lemma 6) | limit point of `φ̄^M` in the product topology on `H^Γ` | (a) | survives verbatim; `H` finite makes `H^Γ` compact, and that is the only compactness used |

Four of six steps transport unchanged.  The two that do not are steps (3) and
(4), and they are two faces of a single fact: **the class must be `Fin`.**

## 3. Why step (3) is the metric-freedom step

[G17] runs two parallel notions.

* **Definition 3**: `(K,L)`-approximability, `L` a class of invariant length
  functions on the groups of `K`.  This is the honest metric notion; hyperlinear
  is `(𝒰, HS)`-approximable for `𝒰 = {U(n)}` and `HS` the single normalized
  Hilbert--Schmidt length on each.
* **Definition 6**: `K`-approximability, *length-free*.  With
  `C_n(X,G) = {x_1^{g_1}···x_n^{g_n}}` the set of `n`-consequences, `G` is
  `K`-approximable if for every finite `Φ` and every `n` there are `H ∈ K` and
  `φ : Φ → H` with `φ(1)=1` such that `φ(Φ∖{1})` is `n`-separated from the
  defect set `{φ(g)φ(h)φ(gh)^{-1}}`.

**Lemma 3 of [G17]** relates them:

> If `G` is `(K,L)`-approximable then it is `K`-approximable; if `G` is
> `K`-approximable then one can define invariant length functions `L` such that
> `G` is `(K,L)`-approximable.

The first half is easy and holds for any fixed metric class: `X = {‖h‖<ε}` and
`Y = {‖h‖ ≥ nε}` gives `n`-separation, because an invariant length satisfies
`‖x^{g_1}_1···x^{g_n}_n‖ < nε`.  **This direction survives for `U(n)` with the
normalized Hilbert--Schmidt length**, which is an invariant length
(`‖uv−1‖₂ ≤ ‖u−1‖₂ + ‖v−1‖₂` and conjugation invariance).

The second half is the metric surgery, and it is where an *arbitrary*
bi-invariant metric is required — see the next section.  For `𝒰` the length is
fixed in advance and cannot be manufactured, so `𝒰`-approximability in the sense
of Definition 6 is strictly weaker than hyperlinearity, with no known way back.

## 4. Glebsky's witnessing length, extracted

This is the object the Hilbert-embeddability criterion has to be applied to.
From the proof of [G17] Lemma 3, verbatim in content:

> Let `X, Y ⊆ H` with `Y` `n`-separated from `X`.  Put
> `X^H = {x^h : x^{±1} ∈ X, h ∈ H}`.  The Cayley graph `Γ(H, X^H)` defines a
> distance `d(h_1,h_2)` = length of a shortest path, or `∞`.  Then
>
> ```text
> ‖h‖ = min{ (1/n) d(1,h), 1 }                                    (GL1)
> ```
>
> is an invariant length function on `H` with `‖x‖ = 1/n` for `x ∈ X` and
> `‖y‖ = 1` for `y ∈ Y`.

So the witnessing metric is the **conjugation-invariant word metric of the
defect set, rescaled by `1/n` and truncated at `1`**.  Three features matter for
the Hilbert-embeddability test:

1. it is a *word* metric with respect to the conjugacy-closed generating set
   `X^H`, not a Hamming-type or rank-type metric.  In particular it is **not**
   of the form of the two calibrating examples in
   `hilbert-embeddable-length-hyperlinearity` (the normalized Hamming length on
   `Sym(n)` is `1 −` (fixed-point fraction), which is not a word length);
2. the truncation `min{·,1}` is not innocuous: conditional negative
   definiteness is not preserved by `ℓ ↦ min{ℓ,1}` in general, so the test must
   be run on the truncated function, not on the word metric;
3. the scaling is harmless.  Glebsky's length gives defect `1/n → 0` against
   separation `1`, so the separation constant is bounded below uniformly, which
   is exactly what a hyperlinear model requires.  Only the character-expansion
   sign condition is at issue.

The finite groups carrying these lengths are supplied by [G17] Proposition 5:
they are the projections `Pr_1^k(X)` of a closed subgroup `X` of a direct
product `∏_i H_i` of groups of `K`, chosen by a compactness argument so that
`C_n(Φ_N, X) ∩ Φ_0 = ∅` survives projection.  **They are therefore finite direct
products of finite quotients of the free cover of `W`, cut to a subgroup**, and
they carry no canonical metric of their own: `(GL1)` is the only metric in play.

## 5. Step (4) provably does not transport

Lemma 4 of [G19] proves `X_N ≠ ∅` by exhibiting the finite group
`D_N ⋊ G_N`, where `D_N = ∏_{M ∈ M_N}(H^{G_M})^m` with `m = |H|^{k|G_M|}`, and
invoking `w̄ ∈ Sys(Fin)` to solve `w̄` **inside it**.  The universal solution
`ū` then lies in `(G_N)^n`, a finite set, and `X = lim_← X_N ≠ ∅` by
compactness of an inverse limit of nonempty finite sets.

For a hyperlinear analogue the system class would be `Sys(𝒰)` = systems solvable
in every `U(n)`, and the step would need

```text
w̄ ∈ Sys(𝒰)  ⟹  w̄ solvable in the finite group D_N ⋊ G_N.
```

**This is false.**  Take `w̄` to be the single equation `x² a^{-1}`.  Every
unitary has a square root, so `w̄ ∈ Sys(𝒰)`.  But `w̄` is not solvable in
`ℤ/2` with `a` the nontrivial element, and `ℤ/2` occurs as a quotient of
`D_N ⋊ G_N` whenever `H = ℤ/2`, which is the lamp of the Kun--Thom wreath.
More generally `Sys(𝒰) ⊄ Sys(Fin)`: Gerstenhaber--Rothaus makes every system
with nonsingular exponent matrix solvable in every compact connected Lie group,
and such systems routinely fail in finite groups.

The conclusion is *not* that `x² = a` obstructs hyperlinearity — that system is
solvable over every group by Higman--Neumann--Neumann.  The conclusion is
sharper and is a statement about the method: **the universal-solution
construction is unavailable for the larger system class, so no amount of
metric bookkeeping repairs the transport.**  This is the exact analogue of what
Glebsky records in his own §7 for the sofic case:

> "Although there is similar characterization of sofic groups: A group `G` is
> sofic if and only if every equation solvable in all permutation groups is
> solvable over `G`.  The problem is that solvability in permutation groups is
> not enough to prove, say, the existence of universal solutions."

Soficity and hyperlinearity fail here for the *same* reason and at the *same*
step.  This is a useful calibration: whatever makes the hyperlinear case hard is
not special to unitaries.

## 6. What the route reduces to

Steps (1), (2), (5), (6) transport.  Steps (3), (4) do not, and cannot be
repaired inside the equational architecture.  So the surviving formulation of
"does Glebsky have a normalized-Hilbert--Schmidt analogue" is **not** "redo the
proof in `‖·‖₂`".  It is:

> **Are the witnessing lengths `(GL1)`, on the finite groups supplied by [G17]
> Proposition 5 for the Kun--Thom wreath `W`, Hilbert embeddable — i.e. does the
> character expansion of `min{(1/n)d_{Γ(H,X^H)}(1,·), 1}` have nonpositive
> coefficients on every nontrivial irreducible?**

A positive answer converts the established `weakly-sofic-not-sofic` witness into
a hyperlinear one (subject to `hilbert-embeddable-length-hyperlinearity`, which
is under adversarial audit and must not be built on until that clears) and
answers Pestov Question 3.4.  A negative answer for the literal `(GL1)` leaves
the asymptotic escape: whether *some* Hilbert-embeddable length family runs the
same `n`-separation witness with defect `→ 0` and uniform separation.  Only the
asymptotic version carries content, since any two invariant lengths on a single
finite group are comparable.

## 7. The character question, made mechanical

Three reductions turn §6 into a finite linear program.

**7.1 The truncation is a red herring.**  Replace `(GL1)` by

```text
ell'(h) = 1 - exp( - d_(Gamma(H,X^H))(1,h) / n ).                (GL2)
```

If `psi` is conditionally negative definite and nonnegative then `1-exp(-psi)`
is conditionally negative definite (Schoenberg: `exp(-psi)` is positive
definite, and `1` minus a normalized positive definite function is
conditionally negative definite).  And `(GL2)` has the same profile as
`(GL1)`: defects have `d=1`, so `ell' = 1-e^(-1/n) ~ 1/n -> 0`, while
`n`-separated elements have `d>n`, so `ell' >= 1-e^(-1) > 0.63`, a separation
constant independent of `n`.  So the truncation `min{.,1}` may be discarded,
and the question is only whether the **untruncated conjugation-invariant word
metric is conditionally negative definite**.

**7.2 Glebsky's length is the pointwise-maximal admissible one.**  If `ell` is
any invariant length with `ell <= 1/n` on `X`, then for
`h = x_1^(g_1) ... x_k^(g_k)` with `x_i^(±1) in X`,

```text
ell(h) <= sum_i ell(x_i^(g_i)) = sum_i ell(x_i) <= k/n,
```

so `ell <= d(1,.)/n` pointwise.  Glebsky's construction therefore takes the
largest length compatible with the defect bound — the one that separates best,
and the one with the least reason to be conditionally negative definite.

**7.3 The shape is exactly the graph's own counterexample.**  The calibration in
`hilbert-embeddable-length-hyperlinearity` records that the `F_2`-rank length on
`GL_2(F_2)` is not Hilbert embeddable.  That length **is** a conjugation-invariant
word metric.  Identify `GL_2(F_2) = S_3`; the rank length is
`rank(g-1)/2 = (0, 1/2, 1/2, 1/2, 1, 1)`, i.e. half the word metric of `S_3`
with respect to the (conjugation-invariant) class of transpositions,
`d = (0,1,1,1,2,2)`.  Expanding `d = a·1 + b·sgn + c·chi` against the class
values `d(e)=0`, `d(tau)=1`, `d(sigma)=2` gives

```text
a + b + 2c = 0,     a - b = 1,     a + b - c = 2,
```

hence `c = -2/3`, `a = 7/6`, and **`b = +1/6 > 0`** on the sign character.  So
conjugation-invariant word metrics are *not* conditionally negative definite in
general, and the smallest nonabelian example already fails.  Glebsky's witnesses
are of precisely this family.  (By contrast the cyclic case is safe: on `Z/m`
with `X={1}` the metric `min{k,m-k}` has nonpositive Fourier coefficients at
every nontrivial character — checked for `m = 3,4,6`, and it is the standard
negative-type circle metric.)

**7.4 Consequently the right question is a feasibility problem, not a
computation of one metric.**  What a hyperlinear model needs is *some*
Hilbert-embeddable invariant `ell` on `H` with `ell <= 1/n` on the defect set
`X` and `ell >= c` on `phi(Phi \ {1})`.  All four constraints are **linear** in
the class function `ell`:

* invariance and `ell(1) = 0`, `ell >= 0`;
* subadditivity `ell(gh) <= ell(g) + ell(h)` — finitely many linear inequalities;
* `ell(x) <= 1/n` for `x in X`, and `ell(y) >= c` for `y in phi(Phi ∖ {1})`;
* conditional negative definiteness: the coefficient of every nontrivial
  irreducible character in the expansion of `ell` is `<= 0`.

So for each finite group `H` this is a **linear program over class functions**,
feasible or not, and infeasibility certificates are exactly LP duals: a positive
combination of characters and subadditivity relations forcing a positive
coefficient.  By 7.2 the program is feasible only if it is feasible *below*
`d/n`, and by 7.3 the upper endpoint `d/n` itself is not in the cone in general.
The live question is whether the cone meets the order interval, which is where
`hilbert-embeddable-witness-for-kun-thom-wreath` already localizes the
difficulty ("the live question is entirely about the middle of the cone").

## 8. Scope

Read in full from the PDF on 2026-08-14: [G19] (all six pages, all lemmas and
proofs); [G17] Definitions 1–8, Lemma 3, Propositions 1, 4, 5, 17, Corollaries
6, 7, Theorem 16, Corollary 19, Proposition 20; DGLT arXiv:1711.10238 §1.1–1.2
(norm conventions and Theorem 1.1).

Proved here: the step classification of §2, the extraction of `(GL1)` in §4, and
the `x² = a` obstruction of §5.

**Not proved here:** that `W` is or is not hyperlinear; that `(GL1)` is or is
not Hilbert embeddable; that no other route from weak soficity to
hyperlinearity exists.  Finding 4 shows the neighbouring Frobenius analogue of
Theorem 1 is false, which is a reason for caution, not a proof.
