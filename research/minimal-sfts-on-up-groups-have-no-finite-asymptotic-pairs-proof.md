---
rg: 2
id: minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs-proof
kind: route
title: Flip one asymptotic pair at occurrences, descend a site potential chosen by Gordan's alternative, and contradict syndetic recurrence
target: minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs
requires: []
---

The notation is that of the target. Imported: Gordan's theorem of the alternative. For a real
matrix `M`, exactly one of the following holds:
- there is a vector `ψ` with `Mψ < 0` in every coordinate;
- there is a vector `a >= 0`, `a ≠ 0`, with `a^T M = 0`.

## 1. The flip lemma

Let `x, x'` be a finite asymptotic pair, `E = Δ(x, x')`, `D = E B^2`, `p = x|_D`, `p' = x'|_D`.
Say `y` has `p'` *at* `g` if `y(gd) = p'(d)` for all `d ∈ D`, and likewise for `p`.

**Lemma 1.** Let `y ∈ X` have `p'` at `g`. Define `z` by `z(ge) = x(e)` for `e ∈ E` and `z = y`
elsewhere. Then `z ∈ X`, `z` has `p` at `g`, and `Δ(y, z) = gE`. The symmetric statement, with
`p` and `p'` exchanged, also holds.

*Proof.* Take `k ∈ Λ`.
- If `kB ∩ gE = ∅`, then `z = y` on `kB`, so `(k^(-1).z)|_B = (k^(-1).y)|_B ∈ W`.
- Otherwise `kb = ge` with `b ∈ B` and `e ∈ E`. So `g^(-1)k = eb^(-1) ∈ EB`, and
  `g^(-1)kB ⊆ EB^2 = D`.
  - For `d ∈ D` we have `y(gd) = x'(d)`, and `z(gd)` is `x(d)` on `E` and `x'(d)` off it.
  - Since `x = x'` off `E`, `z(gd) = x(d)` for all `d ∈ D`.
  - So for `c ∈ B`, `z(kc) = x(g^(-1)kc)`. That is,
    `(k^(-1).z)|_B = ((g^(-1)k)^(-1).x)|_B ∈ W`.

Hence `z ∈ X`. The other two assertions are immediate from `x = x'` off `E`. ∎

## 2. Syndetic occurrences

**Lemma 2.** If `X` is minimal, there is a finite `L_0 ⊆ Λ` such that every `y ∈ X` has `p'` at
some `g ∈ L_0`. The same holds for every finite `L ⊇ L_0`.

*Proof.*
- Let `C = {y ∈ X : y|_D = p'}`. It is clopen and contains `x'`. The point `y` has `p'` at `g` iff
  `g^(-1).y ∈ C`, iff `y ∈ g.C`.
- `U = ∪_g g.C` is open, invariant and nonempty. So `X \ U` is closed and invariant, and it is
  not `X`.
- By minimality `X \ U` is empty, so `U = X`. By compactness finitely many `g.C` cover `X`. ∎

## 3. The potential and its change

Fix a finite `L ⊇ L_0`, and put `Q = LD`, which is finite. For `ψ : Q x A -> R` put
`Ψ(y) = Σ_(k ∈ Q) ψ(k, y(k))`.

Let `y ∈ X` have `p'` at `g ∈ L`, and let `z` be the flip of Lemma 1. Then `Δ(y, z) = gE ⊆ Q`, and
on `gE` we have `y(ge) = x'(e)` and `z(ge) = x(e)`. So

`Ψ(z) - Ψ(y) = Σ_(e ∈ E) [ψ(ge, x(e)) - ψ(ge, x'(e))] = Σ_((k,b) ∈ Q x A) ψ(k, b) ν_b(g^(-1)k) =: (Mψ)_g`.

The right-hand side depends on `g` and `ψ` only, not on `y`. Here `M` is the matrix with rows
`g ∈ L` and columns `(k, b) ∈ Q x A`, with entries `M_(g,(k,b)) = ν_b(g^(-1)k)`.

## 4. Part 1: the alternative

Suppose there were `ψ` with `Mψ < 0`, and put `ε = min_g |(Mψ)_g| > 0`.
- Start from any `y_0 ∈ X`. While `y_i` has `p'` at some `g ∈ L`, let `y_(i+1)` be the flip at
  `g`.
- Each `y_i` lies in `X` by Lemma 1, and `Ψ(y_(i+1)) <= Ψ(y_i) - ε`.
- `Ψ` takes finitely many values, since it depends only on `y|_Q`. So the process stops at some
  `y ∈ X` with `p'` at no `g ∈ L`.
- This contradicts Lemma 2.

So no such `ψ` exists. By Gordan's theorem there is `a : L -> [0, ∞)`, `a ≠ 0`, with
`Σ_(g ∈ L) a(g) ν_b(g^(-1)k) = 0` for all `(k, b) ∈ Q x A`.
- For `k ∉ Q` every term vanishes, because `ν_b(g^(-1)k) ≠ 0` forces `k ∈ gE ⊆ Q`.
- So `a * ν_b = 0` in `R[Λ]` for every `b`. ∎

## 5. Part 2

Take `e ∈ E` and `b = x(e)`. Then `b ≠ x'(e)`, so `ν_b(e) = 1` and `ν_b ≠ 0`. Part 1 gives
`a ≥ 0`, `a ≠ 0`, with `a * ν_b = 0`. This contradicts (NZ). ∎

## 6. Part 3

- **(ii) implies (i).** Let `x, x'` be a finite asymptotic pair with `E = Δ(x, x')`, and put
  `F = EB^2`.
  - For `e ∈ E`, `eB^2 ⊆ F`, so `E ∩ ∂F = ∅`.
  - So `x|_F ≠ x'|_F` agree on `∂F`, and restriction is not injective.
- **(i) implies (ii).** Let `q ≠ q'` in `L_F(X)` agree on `∂F`. Choose `y, w ∈ X` with
  `y|_F = q` and `w|_F = q'`, and let `z` be `y` with `F` overwritten by `q'`. Take `k ∈ Λ`.
  - The patterns `q` and `q'` differ only inside `F \ ∂F`. If `kB` misses `F \ ∂F`, then `z = y`
    on `kB`.
  - If `kB` meets `F \ ∂F` at `s`, then `kB ⊆ sB^2 ⊆ F`, so `z = w` on `kB`.
  - Either way the window is allowed, so `z ∈ X`. Since `Δ(y, z) ⊆ F` is finite and nonempty,
    `(y, z)` is a finite asymptotic pair.
- **The bounds.**
  - Injectivity gives `|L_F(X)| <= |A|^|∂F|`.
  - Over `Z^d`, with `B` inside the cube of side `2r+1`, the set `∂[0,N]^d` lies within distance
    `2r` of the boundary of the cube. So `|∂[0,N]^d| = O(N^(d-1))`. ∎

## 7. Part 4

- **Unique products.** Let finite nonempty `P, P' ⊆ Λ` always have some `k ∈ PP'` with a unique
  representation `k = gh` (`g ∈ P`, `h ∈ P'`). Apply this to `P = supp a` and `P' = supp ν`. Then
  `(a*ν)(k) = a(g)ν(h) ≠ 0`. This uses no sign condition.
- **Bi-orderable groups have unique products.** Let `≤` be a bi-invariant order, `g_0 = max P`
  and `h_0 = max P'`. For `g ≤ g_0` and `h ≤ h_0`, bi-invariance gives `gh ≤ g_0 h ≤ g_0 h_0`, with
  equality iff `g = g_0` and `h = h_0`.
  - Direct products of bi-orderable groups are bi-orderable, by the lexicographic order.
  - `Z^d`, free groups and torsion-free nilpotent groups are bi-orderable (standard facts, not
    re-read).
- **Torsion.** If `t^n = 1` with `n > 1`, then `(1 + t + ... + t^(n-1))(1 - t) = 1 - t^n = 0`. So
  (NZ) fails, and Part 1 then gives no contradiction. ∎

## 8. Part 5

Let `Γ ≤ Λ` have finite index and satisfy (NZ). Write `Λ = ⊔_(t ∈ T) Γt` with `T` finite.

**Recoding.** Put `ι(x)(γ) = (x(γt))_(t ∈ T) ∈ A^T`.
- `ι` is a `Γ`-equivariant homeomorphism onto its image, since
  `(γ'.x)(γt) = x(γ'^(-1)γt)`.
- **Finite type.** Each `tB` meets finitely many cosets `γ_i t_j`. So the `Λ`-window at `γt`
  lies inside `γ(∪_i γ_i t_j)`, and `ι(X)` is a `Γ`-SFT.
- Finite asymptotic pairs correspond under `ι`.

**Normal core.** Put `N = ∩_λ λΓλ^(-1)`, a normal subgroup of finite index. It satisfies (NZ),
because (NZ) passes to subgroups: convolution in `R[N]` is the restriction of convolution in
`R[Λ]`. The recoding above works with `N` in place of `Γ`.

**Minimal components.** Let `X_1` be an `N`-minimal subset of `X`, which exists by Zorn.
- By normality, every `λ.X_1` is `N`-minimal.
  - Two `N`-minimal sets are equal or disjoint.
  - Their union over `λ ∈ Λ` is closed and `Λ`-invariant, so it is `X`.
  - Only `[Λ : N]` of them are distinct, since `λ.X_1` depends only on the coset `λN`.
  - So `X` is a finite disjoint union of closed `N`-minimal sets, each of which is clopen.

**The pair lies in one component.** Let `(x, x')` be a finite asymptotic pair and `χ` the
indicator of the component containing `x`.
- `χ` is continuous and `N`-invariant, so it depends only on `y|_V` for some finite `V`.
- `N` is infinite, so some `ν ∈ N` has `νV ∩ E = ∅`. Then `(ν^(-1).x)|_V = (ν^(-1).x')|_V`.
- So `χ(x') = χ(ν^(-1).x') = χ(ν^(-1).x) = χ(x) = 1`.

The component is `N`-minimal, and it is an `N`-SFT: under `ι` it is the set of points `y` of the
SFT `ι(X)` for which every `(ν^(-1).y)|_V` has `χ = 1`, and that condition is local. It contains
a finite asymptotic pair. This contradicts part 2 for `N`. ∎

## 9. Limits of the argument

- **Positivity is not used in Part 2.** Over unique-product groups the conclusion needs only that
  `R[Λ]` has no zero divisors of the special form `a * ν_b`. Positivity of `a` is recorded because
  it may help over torsion-free groups without unique products, such as the Rips--Segev groups
  (see `kazhdan-groups-without-unique-products-are-zero-divisor-hosts`). Nothing is claimed for
  them here.
- **Infinite difference sets.** The descent needs `Ψ` to change by a fixed amount at every
  occurrence, which uses finiteness of `E`. It says nothing about coarse connectivity of infinite
  difference sets, part 1 of the connected-difference theorems.
