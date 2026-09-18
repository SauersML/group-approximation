---
rg: 2
id: thompson-f-invariant-pivot-orders-cannot-certify-doubling-proof
kind: route
title: Two private points at m give inverse descents g m < m > g^-1 m, which a one-sided invariant order forbids; deep elements are cofinal by common right multiples, and a bi-ordered quotient pins private points to one fiber
target: thompson-f-invariant-pivot-orders-cannot-certify-doubling
requires:
  - thompson-f-nonamenable-iff-some-monomial-set-doubles
  - thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs
  - three-element-doubling-sets-are-free-bases
  - thompson-f-has-no-free-subgroups
  - plo-i-group-is-ea-iff-its-orbital-germ-kernels-are
artifacts:
  - experiments/thompson-f-witness-biography-2026-09-17/pivot_descent.py
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13.md
---

Notation as in the claim. `M` is cancellative, because it sits inside the group `F`.

**Transfer (used in items 4 and 5).** Let `S ⊆ M` be finite. Then `S` doubles in `M` (for finite
`Y ⊆ M`) iff it doubles in `F` (for finite `Z ⊆ F`).
- One direction is trivial.
- For the other, let `Z ⊆ F` be finite. Step 0 of
  `thompson-f-nonamenable-iff-some-monomial-set-doubles-proof` gives `r ∈ M` with `Z r ⊆ M`.
- Right multiplication is a bijection, so `|S Z| = |S Z r| >= 2|Z r| = 2|Z|`.
- For any `g, h ∈ F`, `U` doubles in `F` iff `g U h` does, since `|g U h Z| = |U (h Z)|` and
  `|h Z| = |Z|`.

**Item 1.**
- *Group form.* Let `t_1 ≠ t_2` with `t_1 m`, `t_2 m` private for `m`.
  - `m` is the strict `≺`-maximum of `U^-1 (t_1 m)`, which contains `t_2^-1 t_1 m = g m`, and
    `g ≠ 1`. So `g m ≺ m`.
  - Symmetrically, `t_1^-1 t_2 m = g^-1 m ≺ m`.
- *Monoid form, `m ∈ R(S)`.* Now `g m = s_2^-1 s_1 m` lies in `M` and `s_1 m = s_2 (g m)`, so `g m` is
  a factor of `s_1 m`.
  - It differs from `m` because `s_1 ≠ s_2`, so `g m ≺ m`. Symmetrically, `g^-1 m ≺ m`.

**Item 2.**
- *Nonempty right ideal.*
  - If `m ∈ R(S)` and `n ∈ M`, then `s'^-1 s m n = (s'^-1 s m) n ∈ M`. So `R(S)` is a right ideal.
  - For fixed `s, s'`, the set `I_(s,s') = {m ∈ M : s m ∈ s' M}` is a right ideal. It is nonempty,
    since Step 0 gives `s m = s' u` for some `m, u ∈ M`.
  - Two nonempty right ideals `I, J` meet. Take `i ∈ I`, `j ∈ J`; Step 0 gives `i p = j q` with
    `p, q ∈ M`, which lies in `I ∩ J`.
  - By induction the finite intersection `R(S) = ∩_(s,s') I_(s,s')` is nonempty.
- *Cofinality.* Let `Y` be finite. For each `y ∈ Y`, `{r : y r ∈ R(S)}` is a right ideal. It is
  nonempty: for `m* ∈ R(S)`, Step 0 gives `y p = m* q ∈ R(S)`. Intersecting finitely many gives `r`.
- *Factor set.* For `m ∈ R(S)` and `s ∈ S`, the factors of `s m` are the `m'` with `s m = s' m'`, that
  is `m' = s'^-1 s m`. Each lies in `M` by depth. They are distinct for distinct `s'`, by
  cancellation.

**Item 3.**
- *At most one, group form.* Suppose `t_1 m ≠ t_2 m` are private, and let `g` be as in item 1.
  - *Left-invariant `≺`.* `g m ≺ m` gives `c := m^-1 g m ≺ 1`, by left multiplication by `m^-1`.
    Likewise `g^-1 m ≺ m` gives `c^-1 ≺ 1`. But `c ≺ 1` gives `1 = c^-1 c ≺ c^-1`, by left
    multiplication by `c^-1`. Contradiction.
  - *Right-invariant `≺`.* Right multiplication by `m^-1` gives `g ≺ 1` and `g^-1 ≺ 1`. But `g ≺ 1`
    gives `1 ≺ g^-1`, by right multiplication by `g^-1`. Contradiction.
- *At most one, monoid form, `m ∈ R(S)`.* Item 1 gives the same `g`, and the same contradiction runs
  inside `F`.
- *At least one, left-invariant.* Let `t m` be the `≺`-minimum of the `|U|` distinct elements `U m`.
  For `t'' ≠ t`, `t m ≺ t'' m`, and left multiplication by `t''^-1` gives `t''^-1 t m ≺ m`. So `m` is
  the strict maximum of `U^-1 (t m)`.
- *At least one, right-invariant.* Let `t` be the `≺'`-maximum of `U`, where `a ≺' b ⇔ a^-1 ≺ b^-1`
  (`≺'` is left-invariant).
  - For `t'' ≠ t`, `t'' ≺' t` means `t''^-1 ≺ t^-1`.
  - Right multiplication by `t m` gives `t''^-1 t m ≺ m`.
- *At least one, monoid form.* The competitors of `s m` in `M` are a subset of `S^-1 s m`. So the group
  private point above, which lies in `S m ⊆ M`, is private in the monoid sense.
- *Consequence.* A pivot order needs two private points at every `m ∈ M`, in particular at any
  `m ∈ R(S) ≠ ∅`. A group pivot order needs two at every `m ∈ F`. Both fail.

**Item 4.**
- *Private points lie in `U_λ`.* Let `t m` be private for `m`, either in group form, or in monoid form
  with `m ∈ R(S)`.
  - For every `t'' ∈ U`, `t''^-1 t m ≼ m`. By refinement, `λ(m) <_Γ λ(t''^-1 t m)` is impossible, so
    `λ(t'')^-1 λ(t) λ(m) ≤_Γ λ(m)`.
  - Right-invariance of `<_Γ` gives `λ(t'')^-1 λ(t) ≤_Γ 1`. Right multiplication by `λ(t)^-1` gives
    `λ(t'')^-1 ≤_Γ λ(t)^-1`, that is `λ(t'') ≤' λ(t)`.
  - So `λ(t)` is `≤'`-maximal on `λ(U)`, i.e. `t ∈ U_λ`, and this condition does not involve `m`.
- *Doubling of the fiber, group form.*
  - Each `w` is private for at most one `m`, namely the maximum of `U^-1 w`.
  - For finite `Z ⊆ F`, the private points of the `m ∈ Z` are pairwise disjoint. There are at least
    two for each `m`, and all lie in `U_λ Z`. So `|U_λ Z| >= 2|Z|`.
- *Doubling of the fiber, monoid form.*
  - For finite `Y ⊆ R(S)`, the same count gives `|S_λ Y| >= 2|Y|`.
  - For arbitrary finite `Y ⊆ M`, take `r` with `Y r ⊆ R(S)` (item 2). Then
    `|S_λ Y| = |S_λ Y r| >= 2|Y r| = 2|Y|`.
- *Size.* By the transfer, `S_λ` doubles in `F`.
  - `thompson-f-has-no-free-subgroups` says `F` has no non-abelian free subgroup.
  - Item 2 of `three-element-doubling-sets-are-free-bases` says that then no set of at most three
    elements doubles.
  - Hence `|U_λ| >= 4`.
- *Examples.*
  - `λ = id`, `Γ = F` with a bi-invariant order: `≤'` is total on `F`, so `U_λ` is a single point.
    It cannot double, which recovers item 3 in the bi-invariant case.
  - For the abelianization `F → Z²`, `x_0 ↦ e_1` and `x_i ↦ e_2` for `i >= 1` (the relations
    `x_j x_i = x_i x_(j+1)` are respected).
    - A monomial of degree `d` with `k` letters `x_0` maps to `k e_1 + (d-k) e_2`.
    - Any total order on `Z²` compatible with addition restricts to a strict monotone order in `k`
      on this line, since `e_1 − e_2 ≠ 0`.
    - So `S_λ` consists of the monomials with maximal, or minimal, `k`.

**Item 5.**
- *`|S| >= 4`.* As in the size step of item 4, by the transfer.
- *Degree.* A homogeneous `S` of degree 1 is contained in `X_N = {x_0, ..., x_N}` for some `N >= 1`.
  - The survey's Theorem `xmy`(a), quoted verbatim at line 17 of
    `research/artifacts/thompson-f-monomial-doubling-2026-09-13.md`: "a) For any $m\ge1$, the set of
    elements $X_m=\{x_0,x_1,...,x_m\}$ is not doubling, that is, there exists a finite subset
    $Y\subset M$ such that $|X_mY| < 2|Y|$."
  - A subset of a non-doubling set does not double.
- *The subgroup.* Put `U = s_0^-1 S`; it contains `1` and doubles in `F`, by the transfer and
  translation invariance.
  - Let `H = ⟨U⟩`. For finite `Z ⊆ H`, `|U Z| >= 2|Z|`, with `U Z ⊆ H`.
  - If `H` were amenable, Følner's condition would give `Z ⊆ H` with `|u Z \ Z| < |Z| / |U|` for all
    `u`. Hence `|U Z| < 2|Z|`, as in item 1 of the proof of
    `thompson-f-nonamenable-iff-some-monomial-set-doubles`. That is a contradiction.
  - So `H` is a finitely generated non-amenable, hence non-EA, subgroup of `F ≤ PL_o(I)`. Item 5 of
    `plo-i-group-is-ea-iff-its-orbital-germ-kernels-are` gives the descent.
- *Pivot-order clauses.* These are items 1, 3 and 4.

**Computed notes.** The numbers under "Computed only" in the claim come from
`experiments/thompson-f-witness-biography-2026-09-17/pivot_descent.py`. It uses exact rational PL
maps and the convention `g h = g ∘ h`, checked against `x_j x_i = x_i x_(j+1)` by the script. Positivity
is tested by the domain tree of the reduced diagram being a right vine; that criterion is calibrated
by the script on random positive words and three non-positive elements. The deep seed `m*` has
domain a right vine and range a common refinement on which every `s'^-1 s` is affine with standard
images. These numbers are not used in any step above.
