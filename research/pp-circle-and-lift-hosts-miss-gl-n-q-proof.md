---
rg: 2
id: pp-circle-and-lift-hosts-miss-gl-n-q-proof
kind: route
target: pp-circle-and-lift-hosts-miss-gl-n-q
requires:
  - pp-circle-divisible-subgroups-act-freely
---

Direct deduction from `pp-circle-divisible-subgroups-act-freely`, called the
Theorem below. Not independently reviewed. Let `π : Γ~ -> Γ` be the projection,
with kernel `Z~ = {x -> x + k}`, and let `τ` be the translation number.

## Step 1. Part (a)

Let `D ≤ Γ~` be divisible abelian. Then `π(D) ≤ Γ` is divisible abelian.

- **Homomorphism.** `D` is abelian, so `π(D)` preserves a probability measure
  `μ` on `S^1`. Its periodic lift is preserved by `D`, and the formula of Step 2
  of `pp-circle-divisible-subgroups-act-freely-proof` shows that `τ = τ_μ` is a
  homomorphism on `D`.
- **Injectivity.** Suppose `τ(d) = 0`. Then `rot(π(d)) = τ(d) mod 1 = 0`, so
  `π(d)` has a fixed point. By item 1 of the Theorem, `π(d) = 1`. So `d` is an
  integer translation `x -> x + k` with `τ(d) = k = 0`, and `d = 1`.
- **Normalizers.** `τ` is invariant under conjugation by homeomorphisms of `R`
  that commute with `x -> x + 1`, and `Γ~` consists of such homeomorphisms. So
  `h ∈ N_{Γ~}(D)` gives `τ(h d h^-1) = τ(d)`, and `h d h^-1 = d` by
  injectivity.
- **Amenable subgroups.** If `A ≤ Γ~` is amenable, then `π(A)` preserves some
  `μ`, `A` preserves its lift, and `τ = τ_μ` is a homomorphism on `A` that kills
  `[A, A]`. If `D ≤ [A, A]`, then `τ(D) = 0`, and `D = 1` by injectivity.

## Step 2. Part (b)

Suppose `H` embeds in `Γ` or in `Γ~`, and identify `H` with its image. In the
first case, item 3 of the Theorem says that normalizers of `D` centralize it,
and item 4 excludes `D ≤ [A, A]` for amenable `A`. In the second case Step 1
says the same. Either way, `H` has no subgroup `D` of the kind described in (b).

It remains to exhibit such a `D` in each listed group.

- **`GL_n(Q)`, `SL_n(Q)` (`n >= 2`).** Let `D = {u(q) = I + q E_12 : q ∈ Q}`,
  which is isomorphic to `(Q,+)`, and `h = diag(2, 1/2, 1, ..., 1) ∈ SL_n(Q)`.
  Then `h u(q) h^-1 = u(4q)`, a nontrivial action.
- **`PGL_n(Q)`, `PSL_n(Q)`.** `D` meets the scalar matrices only in `I`, so it
  maps isomorphically onto its image, and the image of `h` still acts by
  multiplication by `4`.
- **`Aff(Q)`, `Aff_+(Q)`, `B_2(Q)`.** Take the translations, normalized by
  `x -> 2x`, which acts by multiplication by `2`.
- **`Q x|_r Z`, `r ≠ 1`.** The generator of `Z` acts by multiplication by `r`,
  which is not the identity.
- **`U_3(Q)` and `U_n(Q)`, `n >= 3`.** These are nilpotent, hence amenable. The
  subgroup `D = {I + q E_13}` is isomorphic to `(Q,+)`, and
  `[I + E_12, I + q E_23] = I + q E_13`, so `D ≤ [U, U]`.

Every group containing one of these contains the same `D`, so it is excluded
too. ∎

## Step 3. Remarks used in the claim

- **Hosts.** Each listed host is a group of piecewise `PSL_2(R)` or PL circle
  homeomorphisms with finitely many breakpoints per element. For the line and
  interval groups, compactify `R ∪ {∞} = RP^1` or glue the ends of `[0,1]`. This
  adds at most one breakpoint.
  - *Finitely generated hosts.* The pieces of the generators generate a finitely
    generated `Λ_0`, which satisfies (D) (Theorem, "Finitely generated hosts").
  - *Hosts with pieces in one `PSL_2(Z[1/N])` or `Aff(Z[1/N])`.* Those groups
    are finitely generated and linear, so they satisfy (D).
- **`T-bar`.** Ghys--Sergiescu proved that every element of `T` has rational
  rotation number. Hence `τ(T-bar) ⊆ Q`, and by Step 1 a divisible abelian
  `D ≤ T-bar` embeds in `Q`. A divisible subgroup of `Q` is `0` or `Q`.
