# A K1-witness is not tracially divisible in any of Fu's senses

Lane: `stw18-k1-witness-strict-comparison-not-k1-injective`, 2026-09-16.

This artifact supports four nodes:

- `fu-exact-simple-tracial-regularity-equivalences` with route
  `fu-exact-simple-tracial-regularity-citation`;
- `strict-comparison-property-tm-forces-sr1` with route
  `fu-lin-property-tm-stable-rank-one-citation`;
- `strict-comparison-tracial-divisibility-forces-sr1` with route
  `strict-comparison-tracial-divisibility-sr1-proof`;
- `stw18-k1-witness-not-tracially-almost-divisible` with route
  `stw18-k1-witness-not-tracially-almost-divisible-proof`.

Nothing here constructs a witness or rules one out. What it proves is that a
witness, if one exists, has no tracial divisibility of any kind in Winter's or
Fu's sense. It also proves that no witness can be a test object for STW
Problem XXVIII.

## 1. Sources and what was read

All statements quoted below were read in the primary source on 2026-09-16.
The arXiv HTML full text was used where one exists, and the LaTeX e-print
source otherwise.

- **[Fu]** Xuanlong Fu, *Divisibility and Real Rank Zero*,
  arXiv:2605.21655v1, submitted 2026-05-20. This is an unrefereed preprint.
  HTML full text read:
  - Theorem 1.1 and the paragraph after it;
  - Definitions 3.1, 3.3, 3.6, 4.3, 7.1, 7.3, 7.5 and 8.1;
  - Remark 3.7;
  - Theorem 8.3;
  - Propositions A.3, A.4 and A.5;
  - Corollaries 9.1, 9.2 and 9.3;
  - bibliography entries [24], [25], [29], [37] and [40].
- **[FL]** Xuanlong Fu and Huaxin Lin, *Tracial oscillation zero and stable
  rank one*, arXiv:2112.14007v4, dated 2024-01-21. Fu's bibliography [24] gives
  the publication as Canad. J. Math. 77 (2025), 563–630. HTML full text read:
  - Theorem 1.1 and the remarks after it;
  - 2.8 and Proposition 2.9;
  - Definitions 2.11 and 2.16;
  - Definition 8.1;
  - Theorem 9.4;
  - Remark 9.10.
- **[Lin]** Huaxin Lin, *Strict comparison and stable rank one*,
  arXiv:2301.09250v2, dated 2024-02-20; J. Funct. Anal. 289 (2025), 111065.
  HTML full text read:
  - Theorem 1.1;
  - Corollaries 1.2, 1.3 and 4.5;
  - Definitions 2.10 and 2.13, with footnote 1;
  - the proof of Theorem 1.1.
- **[W]** Wilhelm Winter, *Nuclear dimension and Z-stability of pure
  C*-algebras*, arXiv:1006.2731v2, dated 2011-05-20; Invent. Math. 187 (2012).
  LaTeX source `perfect-Z-stablev9-inventiones.tex` read:
  - the definition labelled `almost-divisible`, which Fu cites as [40, Definition 3.5];
  - the proposition labelled `divisible-tracially-divisible`, which Fu cites as
    [40, Proposition 3.8];
  - the notation paragraph: "we denote by T(A) the space of tracial states and
    by QT(A) the space of normalized quasitraces".
- **[STW]** C. Schafhauser, A. Tikuisis, S. White, *Nuclear C*-algebras: 99
  problems*, arXiv:2506.10902v2, dated 2026-05-08. LaTeX source
  `Questions-arXiv-Revise.tex` read:
  - Problem XXVIII, the `Q7b` environment;
  - the "folklore" paragraph before Problem XXVII;
  - Theorem [Haagerup, Kirchberg], label `thm:HaagerupQT`;
  - Theorem [APRT, Theorem D], label `PureThm`.
- **Status checks, abstracts and metadata only:**
  - X. Fu, arXiv:2512.23911v1, 2025-12-30;
  - A. S. Toms, arXiv:2609.09535v1, 2026-09-08, a simple AH algebra that is not
    K1-injective and fails strict comparison;
  - L. Robert, arXiv:2609.15776v1, 2026-09-14, *Strict comparison and
    selflessness*.

  None of them produces a strict-comparison nuclear algebra that is not
  K1-injective, or one that is not Z-stable.
- **Not re-read:**
  - Haagerup, *Quasitraces on exact C*-algebras are traces*, C. R. Math. Rep.
    Acad. Sci. Canada 36 (2014). Its statement is used only as quoted in [STW].
  - APRT Theorem D and CETW Section 5, which enter only the novelty audit.
  - Kirchberg–Rørdam's perturbation lemma, which enters only the unpromoted
    remark in Section 6.
  - Rørdam's lemma (R) and the elementary Cuntz facts (C) of Section 3.5. These
    are used as standard inputs, in the same form as the committed direct proof
    `cuntz-sups-with-continuous-rank-converge-uniformly-proof`.

## 2. Verbatim statements used

**[Fu, Theorem 1.1].** "Let A be an algebraically simple separable
non-elementary C*-algebra with QT~(A)≠{0}. Consider the following regularity
properties:

1. Γ:Cu(A)→LAff_+(QT~(A)) is hereditary dense (see Definition 4.3).
2. A has tracial approximate oscillation zero.
3. l^∞(A)/J_A has real rank zero.
4. A is tracially diagonally divisible (see Definition 7.1).
5. A has Property (TM).
6. A is tracially almost divisible.
7. A is tracially m-almost divisible for some m∈N∪{0}.
8. A is weakly tracially diagonally divisible (see Definition 7.3).

Then (1)⇒(2)⇔(3)⇒(4)⇒(5)⇒(6)⇒(7) always holds. If in addition A is exact,
then (7)⇒(8)⇒(1) holds and thus all properties are equivalent."

**[Fu, Corollary 9.2].** "Let A be an algebraically simple separable exact
C*-algebra with QT(A)≠∅. If Cu(A) is m-almost divisible for some m∈N∪{0}, then
l^∞(A)/J_A has real rank zero."

Its proof cites [37, Proposition 2.9(v)] and "[40, Proposition 3.8] for the
unital case" to get tracial m-almost divisibility, and then applies Theorem
1.1. Just before it, Fu recalls the definition: "for all a∈M_∞(A) and all k∈N
there is x∈Cu(A) such that kx≤[a]≤(k+1)(m+1)x ([40, Definition 3.5])".

**[Fu, Definition 3.1].** For τ∈QT~(A) and a C*-subalgebra B of A⊗K,
‖τ|_B‖ := sup{‖τ(b)‖ : b∈Ped(B)^1_+}. Then QT(A) := {τ∈QT~(A) : ‖τ|_A‖=1}, and
T(A) is the set of linear elements of QT(A).

**[Fu, Definition 3.3].** For x∈Ped(A⊗K) and λ∈QT~(A), ‖x‖_{2,λ} = λ(x*x)^{1/2}.
Also ‖x‖_2 = sup{‖x‖_{2,τ} : τ∈closure QT(A)^w}.

**[Fu, Definition 7.5]**, citing [24, Definition 8.1]. "Let A be a C*-algebra with
QT(A)≠∅. We say A has Property (TM) if for all a∈Ped(A⊗K)^1_+, all n∈N, all
ε>0, there is a c.p.c. order zero map φ:M_n→Her(a) such that ‖φ(1_n)a−a‖_2<ε."

**[Fu, Definition 8.1]**, citing [40, Definition 3.5(ii)] and [37, Definition 2.7(iv)].
As printed in the HTML: "... We say A is tracially m-almost divisible, if for
all m∈N and all a∈M_m(A)^1_+, all n∈N, and all ε>0, there is a c.p.c. order
zero map φ:M_n→Her(a) such that τ(1_n)≥(1/(m+1))·τ(a)−ε for all τ∈QT(A)."

The printed text has two typographical slips. The matrix size reuses the
letter `m`, and `τ(1_n)` should be `τ(φ(1_n))`. The definition Fu cites is
Winter's, quoted next, and it has `τ(ψ(1_k))` with an arbitrary matrix size.
Every use below is of Winter's form.

**[W, Definition `almost-divisible`].** "Let A be a unital C*-algebra and m∈N.

- (i) A has m-almost divisible Cuntz semigroup, if for any positive contraction
  a∈M_∞(A) and 0≠k∈N there is x∈W(A) such that k·x≤⟨a⟩≤(k+1)(m+1)·x.
- (ii) We say A is tracially m-almost divisible, if for any positive contraction
  a∈M_∞(A), ε>0 and 0≠k∈N there is a c.p.c. order zero map
  ψ:M_k→her(a)⊂M_∞(A) such that τ(ψ(1_k))≥(1/(m+1))·τ(a)−ε for all τ∈QT(A)."

**[W, Proposition `divisible-tracially-divisible`].** "Let A be a separable,
simple, unital C*-algebra and m∈N. If A has m-almost divisible Cuntz semigroup,
then A is tracially m-almost divisible."

**[FL, Theorem 1.1].** "Let A be a separable simple C*-algebra which admits at
least one densely defined non-trivial 2-quasitrace and has strict comparison.
Then the following are equivalent:

1. A has tracial approximate oscillation zero;
2. Γ is surjective (see 2.13) and A has stable rank one;
3. A has stable rank one;
4. Γ is surjective and A has almost stable rank one;
5. A has property (TM)."

The same page also says: "Note that Theorem 1.1 is stated without assuming
that A is nuclear or exact."

**[FL, Definition 2.11].** "A simple C*-algebra A is said to have (Blackadar's)
strict comparison, if, for any a,b∈(A⊗K)_+, one has a≲b, provided
d_τ(a)<d_τ(b) for all τ∈QT~(A)\{0}."

**[FL, 2.8].**

- "Every unital C*-algebra is compact."
- For compact A: "Denote by QT(A) the set of 2-quasitraces τ with ‖τ|_A‖=1."
- If QT~(A)\{0}≠∅, then R_+·closure QT(A)^w = QT~(A).

**[FL, Definition 2.16].** For a compact T⊂QT~(A), ‖x‖_{2,T} = sup{τ(x*x)^{1/2} : τ∈T}.

**[FL, Definition 8.1].** "Let A be a C*-algebra and S⊂QT~(A)\{0} be a non-empty
compact subset. C*-algebra A is said to have property (TM) relative to S, if
for any a∈Ped(A⊗K)_+, any ε>0, any n∈N, there is a c.p.c. order zero map
φ:M_n→Her(a) such that ‖a−φ(1_n)a‖_{2,S}<ε. A σ-unital simple C*-algebra A with
QT~(A)\{0}≠∅ is said to have property (TM), if for some e∈Ped(A)^1_+\{0},
Her(e) has property (TM) relative to closure QT(A)^w."

**[STW, Problem XXVIII].** "Let A be a unital simple separable nuclear
non-elementary stably finite C*-algebra which has Winter's tracial divisibility
property: for all k,n∈N, ε>0, and non-zero a∈M_k(A)_+, there exists a c.p.c.
order zero map φ:M_n→closure(aM_k(A)a) with τ(φ(1_{M_n}))>τ(a)−ε for all
τ∈T(A). Does A have uniform property Γ?"

**[STW, Theorem (Haagerup, Kirchberg)].** "If A is an exact C*-algebra then all
lower semicontinuous quasitraces on A are traces."

## 3. Hypothesis matching

Throughout this section `A` is unital, simple, separable, exact and
non-elementary, with `T(A) ≠ ∅`.

| [Fu, Thm 1.1 / Cor 9.2] hypothesis | Why `A` satisfies it |
| --- | --- |
| algebraically simple | A nonzero two-sided ideal `I` has nonzero closed closure, which is `A` by simplicity. So `I` contains an element within distance 1 of `1_A`, which is invertible, and so `I = A`. |
| separable, non-elementary | assumed |
| `QT~(A) ≠ {0}`, `QT(A) ≠ ∅` | A tracial state is a normalized quasitrace. Its canonical extension to `A⊗K` is a nonzero element of `QT~(A)`. |
| exact | assumed |

| [FL, Thm 1.1] hypothesis | Why `A` satisfies it |
| --- | --- |
| separable simple | assumed |
| a densely defined non-trivial 2-quasitrace | the extension of `τ ∈ T(A)`, which is finite on `Ped(A⊗K)` |
| strict comparison in the sense of [FL, Def 2.11] | Section 3.5 proves that Blackadar's strict comparison for `M_∞(A)` against `T(A)` alone implies [FL, Def 2.11]. No exactness is needed there. The [FL] form is for `A⊗K` against all nonzero quasitraces, so its premise is stronger. `stw18-k1-witness-constraints-proof` uses the same matching, without proof, when it applies Lin's theorem. |

### 3.1 Fu's Property (TM) gives FL's property (TM)

Assume `A` has Property (TM) in the sense of [Fu, Def 7.5]. Take `e = 1_A`. Since `A` is
unital, `Ped(A) = A`, so `1_A ∈ Ped(A)^1_+ \ {0}` and `Her(1_A) = A`. By
[Fu, Def 3.1] and [FL, 2.8], `QT(A)` is in both papers the set of quasitraces
`τ` with `‖τ|_A‖ = sup_{b ∈ A^1_+} τ(b) = τ(1_A) = 1`. So the two closures
`closure QT(A)^w` are the same compact set `S`, and `0 ∉ S` ([FL, Prop 2.9]).

Now let `a ∈ Ped(A⊗K)_+`, `ε > 0` and `n ∈ N`.

- **If `a = 0`.** The zero map works.
- **Otherwise.** Put `a' = a/‖a‖ ∈ Ped(A⊗K)^1_+`. Note `Her(a') = Her(a)`. [Fu, Def 7.5] gives a c.p.c.
  order zero `φ: M_n → Her(a)` with `‖φ(1_n)a' − a'‖_2 < ε/‖a‖`.

The element `x = φ(1_n)a − a` lies in the ideal `Ped(A⊗K)`. On such elements
[Fu, Def 3.3] and [FL, Def 2.16] both read `sup_{τ ∈ S} τ(x*x)^{1/2}`.
Quasitraces are positively homogeneous, so

```text
‖a − φ(1_n)a‖_{2,S} = ‖a‖·‖φ(1_n)a' − a'‖_2 < ε.
```

Hence `Her(1_A) = A` has property (TM) relative to `S`, which is FL's property (TM).

### 3.2 Winter's Cuntz-semigroup divisibility gives Fu's Corollary 9.2 hypothesis

Assume `W(A)` is `m`-almost divisible in Winter's sense (i). Let `a ∈ M_∞(A)_+`
be nonzero and `k ∈ N`. Then `a/‖a‖` is a positive contraction with the same Cuntz
class, so Winter's `x ∈ W(A)` satisfies `kx ≤ [a] ≤ (k+1)(m+1)x`.

The map `W(A) → Cu(A)` is an order embedding: Cuntz subequivalence of elements of `M_∞(A)`
is the same whether computed in `M_∞(A)` or in `A⊗K`. So the same `x`, read in `Cu(A)`, witnesses the definition Fu
recalls before Corollary 9.2. Also `QT(A) ≠ ∅`. So [Fu, Cor 9.2] gives (3).

Alternatively, [W, Proposition `divisible-tracially-divisible`] applies
directly, because `A` is separable, simple and unital, and gives (7).

### 3.3 Winter's tracial divisibility is Fu's (7)

For a positive contraction `a ∈ M_k(A)`, the hereditary subalgebra
`closure(a (A⊗K) a)` equals `closure(a M_k(A) a) = her(a)`, because
`M_k(A)` is a corner of `A⊗K` containing `a`. So Winter's (ii) with constant `m` is
[Fu, Def 8.1] with the typographical slips corrected, and it is (7).

### 3.4 The XXVIII property gives (6)

Assume `A` has the property of [STW, Problem XXVIII] for positive contractions
only. Take a positive contraction `a ∈ M_k(A)`, together with `n` and `ε`.

- **If `a = 0`.** The zero map satisfies `τ(0) ≥ τ(0) − ε`.
- **If `a ≠ 0`.** XXVIII gives `φ: M_n → closure(aM_k(A)a) = her(a)` with
  `τ(φ(1_n)) > τ(a) − ε` for all `τ ∈ T(A)`.

Every normalized quasitrace is a trace, by [STW, Theorem (Haagerup, Kirchberg)].
In detail, fix `n` and let `τ ∈ QT(A)`.

- **Continuity.** Quasitraces are monotone and additive on commuting elements,
  and `τ(1_{M_n(A)}) = n`. For positive `u, v ∈ M_n(A)`, `u ≤ v + ‖u − v‖·1`, so
  `|τ(u) − τ(v)| ≤ n‖u − v‖`. So `τ` is norm continuous on `M_n(A)_+`, hence
  lower semicontinuous.
- **Linearity.** The theorem applies to the exact algebra `M_n(A)` and makes `τ`
  linear there, equal to `(τ|_A)⊗Tr_n`.

- **Restriction to `A`.** `σ = τ|_A` is linear, positive and tracial, and by
  monotonicity `σ(1_A) = ‖τ|_A‖ = 1`. So `σ ∈ T(A)`.

So on every `M_n(A)`, each `τ ∈ QT(A)` agrees with `σ̄ = σ⊗Tr` for some
`σ ∈ T(A)`. Conversely, every `σ̄` lies in `QT(A)` (Section 3.5, Notation). This
does not identify `QT(A)` with `T(A)` on all of `Ped(A⊗K)`, and nothing below
needs that. The divisibility conditions only evaluate functionals on elements of
some `M_k(A)`. So the XXVIII property for contractions is Winter's (ii) with
`m = 0`, which is (6).

The same argument applies to Winter's normalized quasitraces in (ii), extended
to matrices. On each `M_k(A)` they are the same functionals as Fu's `QT(A)`. So
Section 3.3 involves no mismatch of functionals.

Read literally, without the contraction assumption, the XXVIII property can hold for no unital `A`
with `T(A) ≠ ∅`. For `a = 2·1_A` and `ε < 1`, every c.p.c. `φ` has
`τ(φ(1_n)) ≤ 1 < 2 − ε = τ(a) − ε`. The intended reading is Winter's, with
positive contractions. The repository node
`stw99-problem-xxviii-tracial-divisibility-gamma` copies the literal wording.
This is recorded here and not edited.

### 3.5 Strict comparison on matrices against traces gives [FL, Def 2.11]

**Lemma 3.5.** Let `A` be unital with `T(A) ≠ ∅`. Suppose that for all
`a, b ∈ M_∞(A)_+`, `d_τ(a) < d_τ(b)` for every `τ ∈ T(A)` implies `a ≲ b`.
Then `A` has strict comparison in the sense of [FL, Def 2.11].

This hypothesis is the weakest usual reading of "strict comparison of positive
elements with respect to the trace simplex". No exactness is assumed.

**Notation.**

- For `τ ∈ T(A)`, write `τ̄(x) = Σ_i τ(x_ii)` for `x ∈ (A⊗K)_+`. The `x_ii` are
  the diagonal entries in the matrix units of `K`.
- `τ̄` is the canonical extension, a lower semicontinuous trace on `A⊗K`.
  - The positive elements on which `τ̄` is finite form a hereditary cone that is
    invariant under `x ↦ y*xy`, since `τ̄(y*xy) = τ̄(x^{1/2}yy*x^{1/2}) ≤ ‖y‖²τ̄(x)`.
    So their span is a two-sided ideal, the definition ideal of `τ̄`.
  - That ideal contains the dense subalgebra `∪_n M_n(A)`: each `M_n(A)` is
    spanned by its positive elements, and `τ̄(x) = Σ_{i ≤ n} τ(x_ii) < ∞` there.
  - The Pedersen ideal is contained in every dense two-sided ideal. So `τ̄` is
    finite on `Ped(A⊗K)`.
  - A trace is a 2-quasitrace. So `τ̄` lies in `QT~(A) \ {0}` ([FL, Def 2.7]:
    2-quasitraces defined, with finite values, on `Ped(A⊗K)`).
  - `‖τ̄|_A‖ = τ(1_A) = 1`, so `τ̄ ∈ QT(A)`.
- `f_δ` is 0 on `[0, δ/2]`, 1 on `[δ, ∞)` and linear in between. Also
  `d_τ(x) = sup_δ τ̄(f_δ(x))`, and `f_δ` increases as `δ` decreases.
- `p_n` is the unit of `M_n(A)`, viewed in the multiplier algebra of `A⊗K`.

**Standard inputs**, used in the same form in the committed direct proof
`cuntz-sups-with-continuous-rank-converge-uniformly-proof`:

- **(R) Rørdam's lemma.** If `‖x − y‖ < η` and `t ≥ 0`, then
  `(x − η − t)_+ ≲ (y − t)_+`.
- **(C) Cuntz facts.**
  - `zz* ∼ z*z`.
  - `0 ≤ u ≤ v` implies `u ≲ v`.
  - `g(b) ≲ b` whenever `g ≥ 0` is continuous with `g(0) = 0`.
  - `d_τ` is monotone for `≲`.
  - `a ≲ b` if and only if `(a − ε)_+ ≲ b` for every `ε > 0`.

*Proof.* Let `a, b ∈ (A⊗K)_+` with `d_τ(a) < d_τ(b)` for all
`τ ∈ QT~(A) \ {0}`. In particular this holds for every `τ̄` with `τ ∈ T(A)`.
Scaling changes neither side, so assume `‖a‖ = 1` (the case `a = 0` is
trivial). Fix `ε ∈ (0, 1)`.

1. **Cut `a` into a matrix algebra.**
   - Since `A⊗K` is the closure of `∪_n M_n(A)`, we have `p_n a p_n → a`. Pick
     `n` with `‖a − y‖ < ε/2`, where `y = p_n a p_n ∈ M_n(A)_+` is a contraction.
   - By (R) with `η = t = ε/2`, `(a − ε)_+ ≲ (y − ε/2)_+ =: a_1 ∈ M_n(A)_+`.
   - Put `G(τ) = τ̄(f_{ε/2}(y))`, a finite sum of evaluations of `τ`, so `G` is
     weak* continuous on `T(A)`.
   - **Upper bound on `a_1`.** For `t ∈ [0, 1]`,
     `f_{1/j}((t − ε/2)_+) ≤ f_{ε/2}(t)`: the left side is 0 for `t ≤ ε/2` and at
     most 1 elsewhere, while the right side is 1 for `t ≥ ε/2`. Hence
     `d_τ(a_1) ≤ G(τ)`.
   - **Link to `a`.** `G(τ) ≤ d_τ(y)`. Also `y = zz*` with `z = p_n a^{1/2}`, and
     `z*z = a^{1/2} p_n a^{1/2} ≤ a`, so `y ≲ a` by (C). Hence
     `G(τ) ≤ d_τ(a) < d_τ(b)` for every `τ ∈ T(A)`.
2. **Approximate `b` from below by matrices.**
   - For `k ≥ 1` put `c_k = p_k f_{1/k}(b) p_k ∈ M_k(A)_+` and
     `F_k(τ) = τ̄(c_k) = Σ_{i ≤ k} τ(f_{1/k}(b)_ii)`.
   - Each `F_k` is continuous on `T(A)`.
   - `F_k ≤ F_{k+1}`: there are more summands, and the diagonal entries of
     `f_{1/k}(b) ≤ f_{1/(k+1)}(b)` increase.
   - `F_k(τ) ≤ τ̄(f_{1/k}(b)) ≤ d_τ(b)`.
   - For fixed `k_0` and `k ≥ k_0`, `F_k(τ) ≥ Σ_{i ≤ k} τ(f_{1/k_0}(b)_ii)`. This
     tends to `τ̄(f_{1/k_0}(b))`. So `sup_k F_k(τ) = d_τ(b)`.
   - `c_k = zz*` with `z = p_k f_{1/k}(b)^{1/2}`. Then
     `z*z ≤ f_{1/k}(b) ≲ b`, so `c_k ≲ b` by (C).
3. **Compactness.**
   - The sets `U_k = {τ ∈ T(A) : F_k(τ) > G(τ)}` are open and increasing.
   - They cover `T(A)`, because `sup_k F_k(τ) = d_τ(b) > G(τ)`.
   - `T(A)` is weak* compact, so `U_K = T(A)` for some `K`.
   - `τ̄(c_K) ≤ d_τ(c_K)`. Indeed `c_K` is a contraction in `M_K(A)` and
     `t ≤ f_δ(t) + δ` on `[0, 1]`, so `c_K ≤ f_δ(c_K) + δ p_K`. Hence
     `τ̄(c_K) ≤ τ̄(f_δ(c_K)) + Kδ`, and letting `δ → 0` gives the bound.
   - So for every `τ ∈ T(A)`: `d_τ(a_1) ≤ G(τ) < F_K(τ) = τ̄(c_K) ≤ d_τ(c_K)`.
4. **Conclude.** The hypothesis applies to `a_1, c_K ∈ M_∞(A)_+` and gives
   `a_1 ≲ c_K`. Hence `(a − ε)_+ ≲ a_1 ≲ c_K ≲ b`. Since `ε` was arbitrary,
   `a ≲ b` by (C). ∎

## 4. The derivation

**Theorem A** (`strict-comparison-tracial-divisibility-forces-sr1`). Let `A` be
unital, simple, separable, exact and non-elementary, with `T(A) ≠ ∅`. Assume
strict comparison either for `M_∞(A)` against `T(A)`, as in the hypothesis of
Lemma 3.5, or in the stronger form of [FL, Def 2.11]. Suppose any one of the
following holds:

- (a) `W(A)` is `m`-almost divisible for some `m`;
- (b) `A` is tracially `m`-almost divisible for some `m`;
- (c) `A` has the XXVIII property for positive contractions;
- (d) `A` has one of Fu's properties (1)–(8).

Then `A` has stable rank one.

*Proof.*

1. **Reduce to (d).** (a) gives (3) by Section 3.2. (b) is (7) by Section 3.3. (c) gives (6) by Section 3.4.
2. **Get (TM).** `A` meets the hypotheses of [Fu, Thm 1.1] and is exact. So
   all eight properties are equivalent, and in particular (5) holds.
3. **Transfer (TM).** By Section 3.1, `A` has property (TM) of [FL, Def 8.1].
4. **Conclude.** `A` meets the hypotheses of [FL, Thm 1.1] by the table above.
   Strict comparison in the [FL, Def 2.11] form holds by assumption or by
   Lemma 3.5.
   (5)⇒(3) of that theorem gives stable rank one. ∎

**Theorem B** (`stw18-k1-witness-not-tracially-almost-divisible`). Let `A` be
as in `stw18-k1-witness-strict-comparison-not-k1-injective`: simple, separable,
unital, nuclear and non-elementary, with strict comparison with respect to a
nonempty trace simplex, and not K1-injective. Then (a), (b), (c) and every
one of Fu's (1)–(8) fail for `A`.

*Proof.* Nuclearity gives exactness. Strict comparison of positive elements
against the trace simplex is at least the hypothesis of Lemma 3.5, so Theorem A
applies. If any of (a)–(d) held, Theorem A would give
`sr(A) = 1`. That contradicts item 2 of `stw18-k1-witness-constraints`, which
is Rieffel's theorem that stable rank one gives K1-bijectivity. ∎

### 4.1 Unpacking what fails

For every `m ≥ 0` there are:

- a positive contraction `a ∈ M_k(A)`;
- `n ∈ N` and `ε > 0`;

such that every c.p.c. order zero `φ: M_n → her(a)` has
`τ(φ(1_n)) < τ(a)/(m+1) − ε` for some trace `τ`.

Also:

- **Real rank.** The tracial sequence algebra `l^∞(A)/J_A` does not have real rank zero.
- **Rank map.** `Γ` is not hereditary dense.

Items 2 and 3 of `stw18-k1-witness-constraints` already record that `Γ` is
not surjective and that `A` is not pure. The new content is the tracial and
order-zero failures, uniform in `m`.

## 5. Cross-check and novelty audit

**Chain T.** A second route to `sr(A) = 1` from (2) goes through tracial
oscillation instead of (TM):

- [Fu, Remark 3.7] says Fu's "tracial approximate oscillation zero" is what
  [24, Definition 5.1] calls T-tracial approximate oscillation zero;
- [FL, Theorem 9.4] says strict comparison together with T-tracial approximate
  oscillation zero gives stable rank one.

This agrees with the (TM) route. It is not the promoted route, because
matching Fu's Definition 3.6 to FL's Definition 5.1 needs Fu's remark rather
than a side-by-side reading. The approximants are taken in `Her(a)` in one and
in a Pedersen ideal in the other.

**What was already known.**

- [STW] calls it "folklore that in the presence of strict comparison, all
  these (and other) divisibility conditions coincide and can be used to define
  pureness (see [CETW, Section 5])". CETW Section 5 was not re-read.
- The Cuntz-semigroup half (a) also follows from other sources, none re-read
  here:
  - [STW, Theorem (APRT, Theorem D)]: "Any simple (m,m')-pure C*-algebra is
    already pure";
  - [Lin, Corollary 1.3];
  - `stw58-simple-pure-k1-bijective`.
- So Theorem B is a sourced consolidation, not a new theorem about C*-algebras.

**What it adds to the graph.**

- A dated, hypothesis-matched derivation of the tracial and order-zero
  failures (b), (c) and (d), where [STW] records only folklore.
- The firewall with Problem XXVIII: no K1-witness satisfies the XXVIII
  hypothesis, so none can refute XXVIII, and no answer to XXVIII constrains a
  witness.
- A reusable Theorem A for other lanes. Under strict comparison and exactness,
  Winter's tracial divisibility already forces stable rank one, and hence
  K1-bijectivity, cancellation and surjective `Γ`.

**Remark on [Fu]'s introduction.** Fu writes "Lin [29] showed that (6) is
equivalent to (2) under the same assumption", where [29] is [Lin]. The v2 text
of [Lin] contains no occurrence of "order zero" or of tracial almost
divisibility, so this attribution was not used.

## 6. Consequences and what stays open

- **Design test, not promoted.** The following is the standard density
  argument:
  - If `A = closure(∪ A_i)` and every positive contraction of every `M_k(A_i)` is
    tracially divisible inside `A` with a uniform constant `1/(m+1)`, then `A`
    is tracially `m`-almost divisible.
  - The argument moves order zero maps from `her(φ((a_i − δ)_+))` into
    `her(a)` through Kirchberg–Rørdam's lemma `(b − δ)_+ = d a d*`, followed by
    the trace-preserving isomorphism `her(xx*) ≅ her(x*x)`.
  - By Theorem B, any candidate witness presented as such a limit must, for
    every `m`, contain building-block elements that the connecting maps never
    divide tracially.

  The lemma was not re-read, so this is recorded as a remark only.
- **Unit divisibility.** Theorem B concerns all positive contractions of all
  matrix algebras. It says nothing about the single element `1_A`. Whether a
  witness can have a tracially divisible unit
  (`strict-comparison-forces-tracially-divisible-unit`, OPEN) is untouched. By
  `strict-comparison-unit-divisibility-equivalences`, that would be a witness
  admitting unital `Z_{n,n+1} → A` for every `n`. No argument here excludes it.
- **The target itself stays OPEN.**
