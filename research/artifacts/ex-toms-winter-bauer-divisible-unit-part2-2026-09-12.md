# Toms–Winter on Bauer simplices, part 2: shape of a counterexample and the crux (2026-09-12)

Lane `ex-toms-winter`. Continues `research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md`,
which has the conventions, Definition 1.1, Theorem 1 and Theorem 2.

## 3. Corollary 3: the shape of a counterexample

**Corollary 3.** Let `A` be unital, simple, separable, nuclear and non-elementary, with Bauer
`T(A)`, tlfnd and strict comparison. Suppose `A` is not `Z`-stable. Then:
1. there is `N_0` such that for every `N ≥ N_0` the unit is not tracially `N`-divisible, i.e.
   some `ε_N > 0` has `inf_τ τ(φ(1)) ≤ 1 − ε_N` for every c.p.c. order zero `φ: M_N → A`;
2. for `N ≥ N_0`, `A^U` contains no unital `M_N` and no projection of constant trace `1/N`;
3. `A` has no unital C*-subalgebra that is simple, infinite-dimensional and has a unique
   tracial state;
4. there is `n_0` such that no unital `*`-homomorphism `Z_{n,n+1} → A` exists for `n ≥ n_0`.

*Proof.*
- Items 1 and 2 negate (e) and (d) of Theorem 2.
- For the projection clause of item 2, let `e ∈ A^U` be a projection of constant trace `1/N`.
  Steps 3–6 of Theorem 2 in `research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md`
  use only PC. They place `N` orthogonal equivalent copies of `e` summing to `1`, which is a
  unital `M_N`.
- Item 3 is Lemma 3.1 and item 4 is Lemma 3.2. ∎

**Lemma 3.1.** Let `D ⊂ A` be a unital C*-subalgebra that is simple, infinite-dimensional and
has a unique tracial state `τ_D`. Then the unit of `A` is tracially `N`-divisible for every `N`.

*Proof.*
- `τ_D` is extremal and faithful on the simple `D`. So `π_{τ_D}(D)''` is a finite factor
  containing a copy of `D`. It is infinite-dimensional, hence of type II_1, and it contains a
  unital `M_N`.
- Kaplansky density gives norm-bounded approximate matrix units in `D` for `‖·‖_{2,τ_D}`.
  They define a unital `*`-homomorphism into the tracial ultrapower of `D`. Lifting gives
  c.p.c. order zero `φ_m: M_N → D` with `τ_D(1 − φ_m(1)) → 0`.
- Every `τ ∈ T(A)` restricts to `τ_D` on `D`. So `τ(1 − φ_m(1)) = τ_D(1 − φ_m(1))`, uniformly
  in `τ`. ∎

Examples of such `D`: `Z`, UHF algebras, irrational rotation algebras.

**Lemma 3.2.** For `n > N ≥ 1` there is a c.p.c. order zero map `ψ: M_N → Z_{n,n+1}` with
`tr(ψ(1)(t)) ≥ 1 − N/n` for every `t ∈ [0,1]`. Hence a unital `Z_{n,n+1} ⊂ A` gives
`τ(ψ(1)) ≥ 1 − N/n` for every `τ ∈ T(A)`.

*Proof.* Work in `M_n ⊗ M_{n+1} = M_{n(n+1)}` with normalized trace `tr`.
- Let `π_0: M_N → M_n ⊗ 1` have multiplicity `⌊n/N⌋` in `M_n`, and `π_1: M_N → 1 ⊗ M_{n+1}`
  multiplicity `⌊(n+1)/N⌋` in `M_{n+1}`.
  - In `M_{n(n+1)}` the multiplicities are `a = ⌊n/N⌋(n+1)` and `b = n⌊(n+1)/N⌋`.
  - Both `Na/(n(n+1))` and `Nb/(n(n+1))` are at least `1 − N/n`.
- Say `a ≥ b`; the other case is symmetric. Put `ρ = π_1` and choose `ρ'` of multiplicity
  `a − b` with range orthogonal to that of `ρ`. Then `π_0 = u(ρ ⊕ ρ')u*` for a unitary `u`.
- The path:
  - on `[0,1/3]`, conjugate `ρ ⊕ ρ'` by a unitary path from `u` to `1`;
  - on `[1/3,2/3]`, take `ρ + (2 − 3t)ρ'`;
  - on `[2/3,1]`, take `ρ = π_1`.
- Every value is c.p.c. order zero, the endpoints meet the boundary conditions of `Z_{n,n+1}`,
  and every value contains a unitary conjugate of `ρ`. So its trace is at least `1 − N/n`.
- Every tracial state of `Z_{n,n+1}` integrates the fibre traces `tr(·(t))` against a
  probability measure on `[0,1]`. Restrict the traces of `A`. ∎

**Toms's Villadsen-type algebras.** STW (arXiv:2506.10902, MSI copy line 3381) note that "the
Villadsen-type counterexamples of Toms ([419]) all contain unital copies of Z". This is
consistent with Theorem 2: they are not `Z`-stable, so wherever they have a Bauer simplex and
tlfnd, they fail strict comparison.

**Dadarlat–Hirshberg–Toms–Winter.** DHTW build a unital simple nuclear AH algebra with no
unital `*`-homomorphism from `Z_{3,4}`. So a rigid unit is compatible with simplicity and
nuclearity.
- Their algebra fails strict comparison, since every unital simple AH algebra with strict
  comparison is `Z`-stable (`simple-ah-strict-comparison-is-z-stable`) and so contains `Z`.
- Whether it has a tracially indivisible unit in the sense of Definition 1.1 was not examined.

**Statement fidelity of `stw99-problem-lxv-jiang-su-embeddings`.** That node attributes to
Dadarlat–Toms the expected answer "Z embeds iff B has no nonzero finite-dimensional
representations".
- STW Problem LXV (MSI copy line 3384) asks only: "Characterise those unital (simple)
  C∗-algebras B for which there exists an embedding Z ֒→ B."
- Their footnote 137 records the Dadarlat–Toms question as whether "Z embeds unitally into
  the minimal tensor product D^{⊗∞} whenever D is unital, separable, and has no characters".
- The unrestricted "no finite-dimensional representations" version fails already for a simple
  nuclear AH algebra (DHTW, abstract: "This answers a question of M. Rørdam").

## 4. Attempts on `strict-comparison-forces-tracially-divisible-unit`

- **Through `Z_{n,n+1}` (heuristic, not proved).**
  - Rørdam–Winter (arXiv:0801.2259, Proposition 5.1, not re-read) characterize unital
    `*`-homomorphisms `Z_{n,n+1} → A` by a c.p.c. order zero `φ: M_n → A` and `v` with
    `v*v = 1 − φ(1)` and `φ(e_11)v = v`.
  - Strict comparison should supply `v` once `d_τ(1 − φ(1)) < d_τ(φ(e_11))` at every trace.
    The cut-downs from Cuntz subequivalence to the exact relation were not checked.
  - With Lemma 3.2 the crux would follow from: for large `n`, an order zero `M_n → A` whose
    unit defect has rank below that of one block, everywhere. That is almost `n`-divisibility
    of `[1_A]` in `Cu(A)`: a rank statement at one constant profile.
- **Glimm halving gives uncontrolled profiles.**
  - Glimm's lemma gives `C_0((0,1]) ⊗ M_n → A` inside any hereditary subalgebra, but its rank
    profile is uncontrolled across traces.
  - Greedy orthogonal accumulation adds uncontrolled profiles. Capturing a fixed fraction of
    every remainder at every trace needs an element of rank about half the remainder,
    everywhere: rank density again.
- **The unit carries everything.** By Theorem 1, on Bauer simplices the constant profiles
  `1/N` generate all continuous profiles. So on this locus the whole existence problem behind
  Toms–Winter (RD_b, purity, stable rank one, `Z`-stability) sits at the unit.
- **Where a counterexample must live.**
  - Strict comparison, with DHTW-type rigidity of the unit in a tracially uniform form.
  - Not AH; no unital unique-trace simple subalgebra; no unital `Z_{n,n+1}` for large `n`.
  - An extreme boundary that is locally infinite-dimensional somewhere
    (`bauer-gamma-failure-localizes-to-infinite-dim-point`), and no comparison certificate
    (`strict-comparison-bundle-certificate-vanishes`).
  - In bundle terms: for large `N`, its hyperfinite W*-bundle has no near projection of
    constant trace `1/N` in any reduced power, central or not. Every fibre `R` halves its
    unit, but never uniformly.

## 5. Effect on the graph

- **New, established.**
  - `bauer-tracially-divisible-unit-gives-bounded-rank-density`, route
    `bauer-divisible-unit-rank-density-proof` (direct proof, Section 1).
  - `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`, route
    `toms-winter-bauer-tlfnd-divisible-unit-proof` (Theorem 2, Corollary 3).
- **New, open.**
  - `strict-comparison-forces-tracially-divisible-unit` (Section 4).
  - `toms-winter-holds-on-bauer-tlfnd-locus`, with route
    `toms-winter-bauer-tlfnd-via-divisible-unit` over the two claims above.

## Trust surfaces

- Theorem 1 uses Ozawa's Theorem 3 and the identity `A^u = A^st`, both read on MSI. The
  Winter–Zacharias structure theorem and order zero lifting are standard and were not re-read.
- Theorem 2 chains established claims. Their imports are CETW Theorems 4.6 and A and Vaccaro
  Proposition 1.6.
- Lemmas 3.1 and 3.2 are elementary.
- Not reviewed, and nothing is in Lean.
- Novelty: bounded check only (earlier lanes' literature notes, two web searches on Jiang–Su
  embeddings and on uniform Gamma for Bauer simplices). None is asserted.
