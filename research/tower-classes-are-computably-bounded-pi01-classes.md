---
rg: 2
id: tower-classes-are-computably-bounded-pi01-classes
kind: claim
title: For fixed computable radii and asymmetry bound, margin covering towers form a computably bounded Pi01 class; it is nonempty iff some free minimal subshift has computably bounded moduli, and (M2)-type existence is exactly a computable path
distinct_from:
  covering-towers-iff-effective-minimal-free-subshifts: that proves effective minimal free subshifts exist iff a COMPUTABLE tower exists; this fixes the computable radius data, shows the set of ALL towers (computable or not) for that data is a computably bounded Pi01 class, and identifies its nonemptiness with a non-effective dynamical statement, so effectiveness becomes exactly the selection of a computable path.
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2) itself; this splits (M2) into the non-effective existence statement free-minimal-subshifts-with-computable-moduli-exist and the selection of a computable path in a Pi01 class.
  free-minimal-subshifts-with-computable-moduli-exist: that is the OPEN non-effective existence statement; this proves it is equivalent to nonemptiness of some tower class and is necessary for (M2).
---

**ESTABLISHED** (route `tower-classes-are-computably-bounded-pi01-classes-proof`).

**Setting.** As in `covering-towers-iff-effective-minimal-free-subshifts`:
- `G` is finitely generated with solvable word problem;
- `d(x,z) = |xz^{-1}|`, `(λ.z)(μ) = z(μλ)`, and `w_R(z,h)(μ) = z(μh)` on `B(R)`.

**Two moduli of a subshift.** Let `Y ⊆ A^G` be a nonempty minimal free subshift.
- *Recurrence modulus* `f_Y(r)`: the least `t` such that for every `z ∈ Y`
  and every pattern `p` on `B(r)` occurring in `Y`, some `c ∈ B(t)` has
  `w_r(z,c) = p`.
- *Freeness radius* `R_Y(s)`, for `s ≠ 1`: the least `R` such that every
  `z ∈ Y` has some `μ ∈ B(R)` with `z(μ) ≠ z(μs)`.
- Both are finite, by minimality, freeness and compactness (route, Step 0).

**Data.** A datum `D = (A, (R_n), (m_n), φ)` consists of:
- a finite alphabet `A`;
- computable sequences with `0 ≤ m_n ≤ R_n ≤ R_{n+1}`, `m_n → ∞` and
  `R_n − m_n → ∞`;
- a computable nondecreasing `φ : N → N`.

**Tower class.** `T_D` is the set of all sequences `L = (L_n)` with
`∅ ≠ L_n ⊆ A^{B(R_n)}` that satisfy the conditions below. Computability of `L`
is not required.
- (C) and (K), exactly as in `covering-towers-iff-effective-minimal-free-subshifts`.
- (A_φ): for every `n`, `q ∈ L_n`, `s ≠ 1` and `c` with
  `|c| ≤ R_n − φ(|s|) − |s|`, some `μ ∈ B(φ(|s|))` has `q(μc) ≠ q(μsc)`.
- Put `Y_L = {z : ∀n ∀g ∃h ∈ B(R_n − m_n)g, w_{R_n}(z,h) ∈ L_n}`.

**Theorem.** Let `G` be finitely generated with solvable word problem.
1. *(Pi01.)* `T_D` is the set of infinite paths through a computable tree whose
   branching at depth `N` is bounded by the computable number
   `2^{|A|^{|B(R_N)|}}`. So `T_D` is a computably bounded Π⁰₁ class, and it is
   nonempty iff that tree is infinite.
2. *(Every path gives a subshift.)* For every `L ∈ T_D`, computable or not,
   `Y_L` is a nonempty minimal free subshift with:
   - `R_{Y_L}(s) ≤ φ(|s|)`;
   - `f_{Y_L}(r) ≤ β_D(r) = (R_n − m_n) + (R_{n+1} − R_n) + (R_{n+1} − m_{n+1})`,
     where `n` is least with `m_n ≥ r`. This bound is computable.
   - `Y_L` has a forbidden-pattern set that is decidable relative to `L`.
3. *(Every subshift with computable bounds gives a path.)* Let `Y ⊆ A^G` be a
   nonempty minimal free subshift, not necessarily effective. Suppose
   `f_Y ≤ f̄` and `R_Y(s) ≤ φ(|s|)`, with `f̄` and `φ` computable and `φ`
   nondecreasing. Let `D_Y` be the datum with `R_0 = 2` and `m_0 = 1`, and
   `m_{n+1} = R_n + f̄(R_n)`, `R_{n+1} = 2(R_n + f̄(R_n))`. Then the language
   tower `L_n = L(Y) ∩ A^{B(R_n)}` lies in `T_{D_Y}`.
4. *(The split.)*
   - (N) "`G` carries a nonempty minimal free subshift with computably bounded
     `f_Y` and `R_Y`" holds iff `T_D ≠ ∅` for some computable datum `D`.
   - `G` carries a nonempty effectively closed minimal free subshift iff
     `T_D` has a *computable* member for some computable datum `D`.

**What this changes for (M2).**
- (M2) for an infinite finitely presented `Λ` with solvable word problem
  splits into two parts.
  - (N) is a non-effective existence statement about minimal free subshifts,
    in which only two growth bounds must be computable. It is recorded as
    `free-minimal-subshifts-with-computable-moduli-exist`.
  - *Path selection* is choosing a computable path in a nonempty computably
    bounded Π⁰₁ class `T_D`.
- (M2) ⇒ (N). So a proof that (N) fails for one such `Λ` refutes (M2) for `Λ`
  by pure dynamics, with no computability argument.
- *Class obstruction (precise).* Consider any method that produces a tower
  only by showing the tree of part 1 is infinite: compactness, Zorn, the local
  lemma plus compactness, or Baire and measure genericity inside `T_D`. Such a
  method proves at most (N). It dies at the path-selection step: the invariant
  is the Turing degree of the chosen path. Attempt 1 of (M2) (Zorn inside
  ABT) is an instance.
- *Context only, not imported.* The Jockusch–Soare basis theorems for
  computably bounded Π⁰₁ classes would turn (N) into a tower `L` of low degree,
  and then `Y_L` is Π⁰₁ relative to a low oracle. The same theorems show that
  nonempty such classes need not have computable members, so path selection is
  a genuine step.
