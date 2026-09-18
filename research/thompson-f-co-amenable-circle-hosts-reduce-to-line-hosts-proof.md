---
rg: 2
id: thompson-f-co-amenable-circle-hosts-reduce-to-line-hosts-proof
kind: route
title: Margulis gives the co-amenable subgroup an invariant probability, Eymard lifts it to the host, and the rotation homomorphism leaves interval dynamics
target: thompson-f-co-amenable-circle-hosts-reduce-to-line-hosts
requires:
  - margulis-circle-weak-tits-alternative
  - thompson-f-has-no-free-subgroups
---

Conventions.
- `L ≤ G` is *co-amenable* if `ℓ^∞(G/L)` carries a `G`-invariant mean, that is, a positive
  unital linear functional invariant under `(k·f)(x) = f(k^{-1}x)`.
- For `a, b ∈ S^1`, `[a,b)` is the positively oriented half-open arc from `a` to `b`, and
  `[a,a) = ∅`.

## Lemma 1 (co-amenability calculus)

Let `L ≤ G` be co-amenable, with mean `m` on `G/L`.

(a) **Quotients.** If `π : G → Q` is onto, then `π(L)` is co-amenable in `Q`.
- The map `p : G/L → Q/π(L)`, `gL ↦ π(g)π(L)`, is onto and intertwines `g` with `π(g)`.
- So `f ↦ m(f ∘ p)` is a `Q`-invariant mean.

(b) **Transitivity.** If `M ≤ L` is co-amenable in `L`, with mean `m_L`, then `M` is
co-amenable in `G`.
- For `f ∈ ℓ^∞(G/M)` set `Pf(gL) = m_L(φ_g)`, where `φ_g(hM) = f(ghM)`.
- This is well defined. For `h_0 ∈ L`, `φ_{gh_0} = h_0^{-1}·φ_g`, and `m_L` is
  `L`-invariant.
- `P` is positive and unital and commutes with left translation by `G`. So `m ∘ P` is a
  `G`-invariant mean.

(c) **Finite-index normal subgroups.** Let `N ◁ G` have finite index.
- (c1) `L ∩ N` is co-amenable in `G`.
  - `L ∩ N` is normal in `L`, and `D = L/(L∩N)` is finite.
  - Set `f̄(gL) = |D|^{-1} Σ_{c ∈ D} f(gc)`. It is well defined because left multiplication
    by `h ∈ L` permutes `D`.
  - `f ↦ m(f̄)` is a `G`-invariant mean on `G/(L∩N)`.
- (c2) `L ∩ N` is co-amenable in `N`.
  - Let `m'` be the mean from (c1), and set `X = G/(L∩N)`.
  - The `N`-orbit of `g(L∩N)` is `Ng(L∩N)/(L∩N) = gN/(L∩N)`, using `L∩N ⊆ N`. So there are
    at most `|G:N|` orbits, `X = X_1 ⊔ … ⊔ X_r`, and some `m'(1_{X_j}) > 0`.
  - Then `m_j(f) = m'(f 1_{X_j}) / m'(1_{X_j})` is an `N`-invariant mean on `X_j`.
  - Pick `g` with `X_j = N g (L∩N)`. The map `ψ : N/(L∩N) → X_j`, `x(L∩N) ↦ g x (L∩N)`, is a
    bijection. It satisfies `ψ(n·y) = (gng^{-1})·ψ(y)`, where `n ↦ gng^{-1}` is an
    automorphism of `N`.
  - Hence `f ↦ m_j(f ∘ ψ^{-1})` is an `N`-invariant mean on `N/(L∩N)`.

(d) **Standard facts.**
- A group containing a co-amenable amenable subgroup is amenable: compose `m` with an
  invariant mean on `L`.
- If `L` has an amenable quotient group `L/M`, then `M` is co-amenable in `L`, via the
  invariant mean of the group `L/M`.
- Subgroups, quotients and finite products of amenable groups are amenable. So are
  extensions of an amenable group by an amenable group, and in particular a group with an
  amenable finite-index subgroup.

## Lemma E (Eymard)

If `L ≤ G` is co-amenable and `L` preserves a Borel probability `ν` on a compact `G`-space
`X`, then `X` carries a `G`-invariant Borel probability.

Proof, as in `thompson-f-not-co-amenable-in-known-hosts-proof`:
- `Pφ(gL) = ∫ φ(gx) dν(x)` is well defined on `G/L` for `φ ∈ C(X)`.
- `φ ↦ m(Pφ)` is a positive, unital, `G`-invariant functional on `C(X)`.
- Riesz representation turns it into the required measure. ∎

## Lemma R (circle groups with an invariant probability)

Let `Γ ≤ Homeo_+(S^1)` preserve a Borel probability `μ`.

(R0) **Arc additivity.** `μ([a,b)) + μ([b,c)) ≡ μ([a,c)) (mod 1)`.
- If `b ∈ [a,c)`, or `b = a`, the two arcs partition `[a,c)`.
- Otherwise their union covers `S^1` once and `[a,c)` a second time.

(R1) **Rotation homomorphism.** `ρ(g) = μ([x,gx)) mod 1` does not depend on `x`, and it is
a homomorphism.
- By (R0), `μ([y,gy)) ≡ μ([y,x)) + μ([x,gx)) + μ([gx,gy))`.
- Since `g` preserves orientation, `g[x,y) = [gx,gy)`, so `μ([gx,gy)) = μ([x,y))`. Also
  `μ([y,x)) + μ([x,y)) ≡ 0`.
- Hence `μ([y,gy)) ≡ μ([x,gx))`.
- `ρ(gh) ≡ μ([x,hx)) + μ([hx,ghx)) = ρ(h) + ρ(g)`, where the second term is `ρ(g)` computed
  at the base point `hx`.

(R2) **The kernel fixes the support.** `K = ker ρ` fixes `supp μ` pointwise.
- Let `g ∈ K`, `x ∈ supp μ`, and suppose `gx ≠ x`. Then `μ([x,gx)) + μ([gx,x)) = 1` with
  `μ([x,gx)) ∈ Z`, so one of the two arcs is null.
- Replacing `g` by `g^{-1}` if needed, we may assume `μ([x,gx)) = 0`. This uses
  `g^{-1}[gx,x) = [x, g^{-1}x)`.
- Then also `μ([g^{-1}x, x)) = μ(g^{-1}[x,gx)) = 0`.
- If `g^{-1}x ∈ [x,gx)`, the null arcs `[g^{-1}x,x)` and `[x,gx)` cover `S^1`, which is
  absurd.
- Otherwise `g^{-1}x ∈ [gx, x)`. Then the union `[g^{-1}x,x) ∪ [x,gx)` is either the arc
  that runs from `g^{-1}x` through `x` to `gx`, or all of `S^1` when `g^{-1}x = gx`. Either
  way it is a null set containing an open neighbourhood of `x`, contradicting `x ∈ supp μ`.

(R3) **An element preserving a gap lies in `K`.** Let `J` be a component of
`S^1 \ supp μ` with `supp μ` not a single point.
- Then `J = (p,q)` with `p ≠ q` both in `supp μ`.
- If `gJ = J`, then `g` preserves orientation, so `gp = p`, and `ρ(g) = μ([p,p)) = 0`.
- Conversely `K` fixes `p` and `q` by (R2), so it maps the positive arc `(p,q)` onto itself.

## Proof of the claim

Let `H ≤ G ≤ Homeo(S^1)` with `H` co-amenable and without non-abelian free subgroups.
- `G^+ = G ∩ Homeo_+(S^1)` is normal of index at most 2 in `G`.
- Put `H^+ = H ∩ G^+`.

**1 (measure).**
- `H^+ ≤ Homeo_+(S^1)` has no non-abelian free subgroup. By
  `margulis-circle-weak-tits-alternative` it preserves a Borel probability `ν`.
- By Lemma 1(c1) with `N = G^+`, `H^+` is co-amenable in `G`.
- Lemma E, applied to `ν` on the compact `G`-space `S^1`, gives a `G`-invariant probability
  `μ`.

**2 (rotation part).** Apply Lemma R to `Γ = G^+`. Then `ρ(G^+) ≤ R/Z` is abelian, so
`[G^+,G^+] ≤ K`.

**3 (full support).**
- If `supp μ = S^1`, then `K` acts trivially by (R2). So `K = 1` and `G^+ ≅ ρ(G^+)` is
  abelian.
- `H^+ ≤ G^+` is then an abelian subgroup of `H` of index at most 2.
- If `G` is minimal, `supp μ` is a nonempty closed `G`-invariant set, hence all of `S^1`.

**4 (atoms).**
- Only finitely many atoms have mass at least any given `ε > 0`. So the atoms of maximal mass
  form a finite nonempty `G`-invariant set, which contains a finite orbit `O`.
- Let `G_1` be the intersection of `G^+` with the kernel of `G → Sym(O)`. It is normal of
  finite index in `G`.
- `S^1 \ O` has `n = |O|` components `J_1, …, J_n`. These are open arcs, and
  `J_1 = S^1 \ {p}` when `n = 1`.
- An element of `G_1` fixes the endpoints of each `J_i` and preserves orientation, so it maps
  the positive arc between them onto itself.
- An element of `G_1` that is trivial on every `J_i` also fixes `O`, so it is the identity.
  Hence `G_1 ↪ ∏_i Q_i`, where `Q_i` is the image of `G_1` in `Homeo_+(J_i) ≅ Homeo_+(R)`.
- Assume `G` is non-amenable. Then `G_1` is non-amenable, and by Lemma 1(d) some `Q_i` is
  non-amenable.
- By Lemma 1(c2) with `N = G_1`, `L_1 = H ∩ G_1` is co-amenable in `G_1`. By Lemma 1(a),
  `π_i(L_1)` is co-amenable in `Q_i`.
- `L_1` has index at most `|G:G_1|` in `H`.

**5 (atomless, not full).**
- `supp μ` is not a point, since `μ` has no atom. So every gap is an arc `(p,q)` with
  `p ≠ q` in `supp μ`. There are countably many gaps, and `G^+` permutes them.
- By (R3) every gap has stabilizer exactly `K`.
- An element of `K` trivial on every gap is the identity, since it fixes `supp μ` by (R2). So
  `K ↪ ∏_J Homeo_+(J)`.
- `H^+` is co-amenable in `G^+` by Lemma 1(c2).
- `H^+/(H^+ ∩ K)` embeds in the abelian group `ρ(G^+)`. So `H ∩ K = H^+ ∩ K` is co-amenable
  in `H^+` by Lemma 1(d), and in `G^+` by Lemma 1(b).
- If `K` were amenable, so would be `G^+` (abelian quotient) and then `G`.

## Specialization to Thompson's group `F`

`F` has no non-abelian free subgroup (`thompson-f-has-no-free-subgroups`).

**(F1) No finite-index subgroup of `F` is abelian.** Work in the standard model on `[0,1]`.
- `x_0` is `t/2`, `t − 1/4`, `2t − 1` on `[0,1/2]`, `[1/2,3/4]`, `[3/4,1]`.
- `x_1` is `t`, `t/2 + 1/4`, `t − 1/8`, `2t − 1` on `[0,1/2]`, `[1/2,3/4]`, `[3/4,7/8]`,
  `[7/8,1]`.
- Then `x_0(t) < t` on `(0,1)`, and `x_1(t) < t` on `(1/2,1)`. So for every `m ≥ 1` the
  support of `x_1^m` is `(1/2,1)`.
- Let `L ≤ F` have index `n`. Two of the cosets `x_0^j L` (`0 ≤ j ≤ n`) coincide, so
  `x_0^k ∈ L` for some `1 ≤ k ≤ n`. Likewise `x_1^{k'} ∈ L`. Put `m = kk'`.
- `x_0^m x_1^m x_0^{-m}` has support `(x_0^m(1/2), 1) ≠ (1/2,1)`. So `x_0^m` and `x_1^m`
  do not commute, and `L` is not abelian.
- Hence case 3 cannot occur for `H = F`, and no minimal `G` contains `F` co-amenably. `T` acts
  minimally on `S^1` (its orbits contain all dyadic rotates, see
  `thompson-t-is-not-amenable-proof`), so no copy of `F` in `T` is co-amenable.

**(F2) Case 4 gives a faithful co-amenable copy of `F'`.** Import, verbatim: Navas,
arXiv:math/0607481, `navas.tex` l.1726–1727: "(One may also use the nontrivial fact that the
derived group $[\mathrm{F},\mathrm{F}]$ is simple \cite{CFP}.)"
- `F' = [F,F]` is infinite and simple, so it has no proper finite-index subgroup. (The normal
  core of one would be a proper nontrivial normal subgroup.)
- `F' ∩ L_1` has finite index in `F'`, so `F' ≤ L_1`.
- `ker(π_i|_{F'})` is normal in `F'`, so it is `1` or `F'`.
- If it were `F'`, then `π_i(L_1)` would be a quotient of the abelian group `L_1/F'`. It
  would then be an amenable co-amenable subgroup of `Q_i`, making `Q_i` amenable. That is
  impossible.
- So `π_i` is injective on `F'`. Moreover `π_i(F')` is normal in `π_i(L_1)` with abelian
  quotient, so it is co-amenable in `Q_i` by Lemma 1(d) and (b).
- `F` is non-amenable iff `F'` is, because `F/F'` is abelian.

**(F3) Recovering the standard case.** For the standard action of `F` on `[0,1]/(0∼1)`, the
only `F`-invariant probability is `δ_0`: see Lemma I of
`thompson-f-not-co-amenable-in-known-hosts-proof`. Then `μ = δ_0` and `G` fixes `0`. ∎

## Trust surface

- Margulis's theorem, imported verbatim through Navas (`margulis-circle-weak-tits-alternative`).
- Simplicity of `[F,F]`, imported verbatim through Navas l.1726–1727, which cites
  Cannon–Floyd–Parry. It is used only in (F2).
- Everything else is proved in place.
