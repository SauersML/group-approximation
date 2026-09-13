# Sofic set actions: restriction to co-amenable subgroups, finite-index induction, local separation

Lane `ex3-pfg-positive`, 2026-09-13. Unreviewed.

Soficity of an action `α : G ↷ X` of a countable group on a countable set is
Gao--Kunnawalkam Elayavalli--Patchell (GKP), arXiv:2401.04945v3, Definition
2.1(5), read from the v3 PDF on 2026-09-13. For finite `F ⊆ G`, `E ⊆ X` and
`ε > 0` there must be a finite set `A` and a unital, `(F, ε)`-multiplicative map
`φ : G → Sym(A)` that is an `(F, E, ε)`-orbit approximation. That means there
are a finite set `B`, a set `S ⊆ A` with `|S| > (1-ε)|A|`, and injective labels
`π_s : E ↪ B` (`s ∈ S`), such that

```text
π_(φ(g)s)(x) = π_s(α(g^-1)x)   whenever s ∈ S, g ∈ F, x ∈ E, φ(g)s ∈ S, α(g^-1)x ∈ E.   (OA)
```

Throughout, `F` is enlarged to be symmetric and to contain `1`.

## 1. Restriction to a co-amenable subgroup

`H ≤ G` is *co-amenable* if `G ↷ G/H` has an invariant mean. Equivalently,
by the Følner characterization of amenable actions (Rosenblatt; Greenleaf),
for every finite `F ⊆ G` and `δ > 0` there is a finite nonempty `Φ ⊆ G/H`
with `|gΦ △ Φ| < δ|Φ|` for all `g ∈ F`.

**Theorem 1.1.** Let `H ≤ G` be co-amenable and `α : G ↷ X` an action on a
countable set. If the restriction `α|_H` is sofic, then `α` is sofic.

The converse is GKP Proposition 2.15(3). So soficity of an action can be
tested on any co-amenable subgroup.

*Proof.* Fix finite `F ⊆ G`, `E ⊆ X` and `ε > 0`. Choose a section
`σ : G/H → G` with `σ(H) = 1`, and the cocycle

```text
c(g, y) = σ(gy)^-1 g σ(y) ∈ H          (g ∈ G, y ∈ G/H),
c(gh, y) = c(g, hy) c(h, y).
```

Choose `δ > 0`, and a Følner set `Φ ⊆ G/H` for the finite set `F·F` with
constant `δ`. Put

```text
F_H = { c(g, y) : g ∈ F·F, y ∈ Φ } ∪ {1},        E_H = { σ(y)^-1 x : y ∈ Φ, x ∈ E }.
```

Both are finite. Take a unital `(F_H F_H, ε')`-multiplicative map
`ψ : H → Sym(A_H)` that is an `(F_H, E_H, ε')`-orbit approximation of `α|_H`,
with good set `S_H` and labels `π^H_a : E_H ↪ B`.

*The model.* Put `A = Φ × A_H`. For `g ∈ G` define `φ(g)` on
`(Φ ∩ g^-1Φ) × A_H` by

```text
φ(g)(y, a) = (gy, ψ(c(g,y)) a).
```

This is injective and lands in `Φ × A_H`. Extend it to a permutation of `A` by
any bijection between the complements, which have equal size. Since `c(1,y) = 1`
and `ψ(1) = 1`, `φ(1) = 1`.

*Multiplicativity.* Let `g, h ∈ F` and `y ∈ Φ ∩ h^-1Φ ∩ (gh)^-1Φ`. All three
maps are then given by the formula, and

```text
φ(g)φ(h)(y,a) = (ghy, ψ(c(g,hy)) ψ(c(h,y)) a),    φ(gh)(y,a) = (ghy, ψ(c(g,hy)c(h,y)) a).
```

`c(g,hy)` and `c(h,y)` lie in `F_H`. So the two agree for a proportion
`> 1-ε'` of `a`. The excluded `y` form a proportion `< 2δ` of `Φ`. Hence
`d(φ(gh), φ(g)φ(h)) < 2δ + ε'`.

*Orbit approximation.* Let `Φ_0 = { y ∈ Φ : gy ∈ Φ for all g ∈ F }`. Then
`|Φ_0| > (1 - |F|δ)|Φ|`. Put `S = Φ_0 × S_H`, so `|S| > (1-|F|δ)(1-ε')|A|`.
For `s = (y, a) ∈ S` and `x ∈ E` put

```text
π_s(x) = π^H_a( σ(y)^-1 x ).
```

This is defined because `σ(y)^-1 x ∈ E_H`, and it is injective in `x`.

Now let `s = (y,a) ∈ S`, `g ∈ F`, `x ∈ E`, with `φ(g)s ∈ S` and
`α(g^-1)x ∈ E`. Since `y ∈ Φ_0`, `φ(g)s = (gy, ψ(k)a)` with `k = c(g,y) ∈ F_H`,
and `ψ(k)a ∈ S_H`. Put `z = σ(gy)^-1 x ∈ E_H`. Then

```text
α(k^-1) z = σ(y)^-1 g^-1 σ(gy) σ(gy)^-1 x = σ(y)^-1 α(g^-1)x ∈ E_H.
```

So (OA) for `ψ` applies to `a`, `k`, `z`:

```text
π_(φ(g)s)(x) = π^H_(ψ(k)a)(z) = π^H_a(α(k^-1)z) = π^H_a(σ(y)^-1 α(g^-1)x) = π_s(α(g^-1)x).
```

Choosing `δ` and `ε'` small makes `φ` an `(F, E, ε)`-orbit approximation. `∎`

**Special cases.**

- `H` the stabilizer of a point of a transitive amenable action. This gives
  the `⇐` direction of `co-amenable-induction-of-sofic-actions`, whose proof is
  the same construction. The theorem needs neither transitivity nor for `H` to
  be a stabilizer.
- `H = {1}`, which is co-amenable exactly when `G` is amenable. Every action of
  the trivial group is sofic, so this recovers GKP Theorem 2.17.
- `H` of finite index: soficity passes from a finite-index subgroup to the
  whole action.

**Corollary 1.2 (finite-index induction).** Let `H ≤ G` have finite index and
`β : H ↷ Y` be sofic. Then `G ↷ G ×_H Y` is sofic.

*Proof.* Let `H_0 = core_G(H)`, which is normal and of finite index. Fix a
transversal `t_1, …, t_d` of `G/H`. The induced set is `⊔_i t_i × Y`. For
`h_0 ∈ H_0` we have `h_0 t_i = t_i (t_i^-1 h_0 t_i)` with `t_i^-1 h_0 t_i ∈ H_0`.
So each sheet `t_i × Y` is `H_0`-invariant, and `H_0` acts on it by `β`
restricted to `H_0` and composed with the automorphism `h_0 ↦ t_i^-1 h_0 t_i`.

- Restriction to a subgroup preserves soficity (GKP 2.15(3)), and so does
  precomposition with a homomorphism, since models compose.
- A finite union of sofic `H_0`-sets is sofic (GKP 2.16).

So the induced action restricted to `H_0` is sofic, and Theorem 1.1 finishes. `∎`

**Corollary 1.3 (groups).** If `G` has a co-amenable sofic subgroup `H`, then
`G` is sofic.

*Proof.* The left action `G ↷ G` restricts to a free action of the sofic group
`H`. That action is sofic: its orbits are copies of `H ↷ H`, which is sofic by
GKP Theorem 2.14 with `N = 1`, then apply Proposition 2.16. By Theorem 1.1,
`G ↷ G` is sofic. GKP Theorem 2.12 (p. 6) states: "In particular, if the left
multiplication action `α : G ↷ G` is sofic, then `G` is sofic." `∎`

The normal case is Elek--Szabó's amenable extension theorem. The literature
was not searched for the non-normal case, which is probably known.

## 2. Local separation

**Lemma 2.1.** Let `α : G ↷ X`. Suppose that for every finite symmetric
`F ∋ 1` and finite `E ⊆ X` there are a sofic action `β : G ↷ Y` and an injective
map `ι : E → Y` with

```text
ι(α(g)x) = β(g) ι(x)     whenever g ∈ F and x, α(g)x ∈ E.            (PE)
```

Then `α` is sofic.

*Proof.* Take a model `ψ` of `β` for `(F, ι(E), ε)`, with good set `S` and
labels `π^Y_s`. Put `π_s(x) = π^Y_s(ι(x))`, which is injective. Suppose
`s ∈ S`, `g ∈ F`, `x ∈ E`, `ψ(g)s ∈ S` and `α(g^-1)x ∈ E`. By (PE) applied to
`g^-1` and the point `x`, `β(g^-1)ι(x) = ι(α(g^-1)x) ∈ ι(E)`. So (OA) for `ψ`
gives

```text
π_(ψ(g)s)(x) = π^Y_s(β(g^-1)ι(x)) = π^Y_s(ι(α(g^-1)x)) = π_s(α(g^-1)x).   ∎
```

Two known statements are special cases:

- (S1) of `separating-sofic-quotient-sets-make-an-action-sofic`: a global
  equivariant map injective on `E`.
- Proposition 30.3 of the dossier (`GroupApproximation/Sofic/SoficActionChabauty.lean`):
  larger subgroups that agree with `H` on finitely many tests.

Lemma 2.1 needs neither a globally defined map nor a coset space of a larger
subgroup. Part 2 uses it with a product `Y` whose base-point stabilizer is
*smaller* than the stabilizer of the approximated point.
