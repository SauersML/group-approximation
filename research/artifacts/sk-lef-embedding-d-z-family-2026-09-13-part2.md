# sk-lef-embedding-d: subgroups of the Z-family G_X (part 2)

## 2. Banded representations of finitely presented subgroups

**Proposition B.** Let `X` be an infinite minimal Z-subshift and `Γ = ⟨S⟩` a finitely presented group, with
`S = S^{-1}` finite. Let `ρ : Γ -> GL_m(R_X)` be an injective homomorphism, and let `w` bound the exponents of `u` in
the entries of `ρ(s)`, `s ∈ S`. Then for every `r` there are `N ≥ r` and a homomorphism `π : Γ -> GL_(mN)(F_2)` such
that:
- `π` is injective on the ball `B_Γ(r)`;
- each `π(s)` is *cyclically w-banded*. Write `F_2^(mN) = ⊕_(n ∈ Z/N) F_2^m`. The block `(n,n')` of `π(s)` is zero
  unless `n−n' ∈ {−w,…,w}` mod `N`.

*Proof.*
1. Fix a finite presentation `⟨S | Rel⟩` and a finite list `P` of sums and products in `M_m(R_X)`:
   - the successive products that evaluate `ρ(v)` for every relator `v ∈ Rel` and every word `v` of length ≤ r;
   - the differences `ρ(g) − ρ(h)` for `g ≠ h ∈ B_Γ(r)`.
2. The periodic models `Φ = Φ_y : Σ f_ju^j ↦ Σ D_y(f_j)P^j` of the note's finite-models step, applied entrywise and
   with window and period large, preserve every operation in `P` and keep its nonzero listed elements nonzero
   (`subshift-lef-models-period-below-twice-recurrence`).
3. Put `π(s) = Φ(ρ(s))`. Inductively `π(v) = Φ(ρ(v))` for every listed word `v`.
4. For a relator, `π(v) = Φ(I) = I`, so `π` is a homomorphism from `Γ`. Since `s^{-1} ∈ S`, `π(s)π(s^{-1}) = I`, so
   `π(s) ∈ GL_(mN)(F_2)`.
5. For `g ≠ h ∈ B(r)`, `π(g) − π(h) = Φ(ρ(g) − ρ(h)) ≠ 0`.
6. `D_y(f)P^j` with `|j| ≤ w` is supported on cyclic distance ≤ w, which gives the banding. ∎

**Corollary B1.** A finitely presented subgroup of some `G_X` is residually finite. For a finitely presented `Γ`,
genuine finite representations that are injective on every ball force residual finiteness.

**Corollary B2 (obstruction test).** Let `Γ` be finitely presented. Suppose that for every `w` there is an `r` such that
no homomorphism `Γ -> GL_N(F_2)`, for any `N`, with cyclically w-banded generators in blocks of size `m`, is injective
on `B_Γ(r)`. Then `Γ` is a subgroup of no `GL_m(R_X)`, hence of no `G_X`.

## 3. Linear orbit growth (any f.g. subgroup)

**Proposition C.** Let `Γ = ⟨S⟩ ≤ GL_m(R_X)` be f.g., with `w` as above.
- `R_X` is simple, so for every `x ∈ X` the orbit representation on `V_x = ⊕_(n∈Z) F_2^m` is faithful.
- Each `s ∈ S` moves supports by at most `w`. If `v` is supported on an interval of length `L`, then
  `dim span(B_Γ(r)·v) ≤ m(L+2wr)`.
- The same bound holds for the image of `v` in every subquotient module of `V_x`.

So `V_x` is a faithful module in which every cyclic submodule, and every subquotient, grows at most linearly along
balls.

## 4. Model tests

- **Free group `F_2`** (passes, and it is a subgroup of `G_X`). `SL_2(F_2[t])` contains a free group, and reduction
  `F_2[t^{±1}] -> F_2[t]/(t^N−1)`, `t ↦ P`, gives banded representations of width 1, injective on large balls.
- **Finitely presented non-RF groups** (fail B1 as they should). Thompson's `V` is an example.
- **`G_X` itself**: not finitely presented, so Proposition B does not apply. Proposition C holds.

## 5. Test object `SL_3(Z)`

`SL_3(Z)` is finitely presented, Kazhdan and residually finite, with the congruence subgroup property. So every
homomorphism `SL_3(Z) -> GL_N(F_2)` factors through some `SL_3(Z/M)`.
- By B2, `SL_3(Z) ≤ G_X` requires w-banded F_2-representations of congruence quotients that are injective on balls of
  every radius, with `w` fixed.
- **Permutation encodings die.** The Schreier graphs of `SL_3(Z/M)` on vectors are expanders (property (T)). An
  expander on `N` vertices has bandwidth ≥ cN: an interval cut of a w-banded arrangement has at most `2w|S|m` edges,
  while expansion forces at least `h·N/2`. So no permutation basis is banded with bounded width.
- **Linear flexibility.** The natural module of `SL_n(F_2)` is 1-banded for the note's generators, although its
  Cayley graphs are expanders. So Cayley-graph expansion does not obstruct banding.
- **The real obstruction would be dimension expansion.** Suppose every F_2-module factor of the finite models had
  uniform dimension expansion and unbounded dimension. Proposition C then bounds the factor dimensions, a contradiction.
  Whether this holds for `SL_3(Z/M)` in characteristic 2 (cross characteristic for odd `M`) is not known to this lane.
