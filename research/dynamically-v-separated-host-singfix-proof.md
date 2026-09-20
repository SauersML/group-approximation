---
rg: 2
id: dynamically-v-separated-host-singfix-proof
kind: route
title: Every one- and two-point SingFix group of the annular host is an iterated ascending HNN extension of V_(2,r) x| G^k, so Belk--Hyde--Matucci Theorem 2.1 applies
target: dynamically-v-separated-groups-satisfy-boone-higman
requires:
  - germ-complex-and-bux-gonzalez-morse-inputs
  - fp-clopen-transitive-full-cantor-groups-have-type-a-actions
artifacts:
  - research/artifacts/beyond-polynomial-germs/mapping-tori-and-compact-core.md
---

Notation as on the claim. Put `ρ_n = ρ ∘ φ^n`. Write `B_n = V(C ∖ 0^n C)`, the elements of
`V` that are the identity on `0^n C`, and `K_p = ⋃_n B_n`.

**Later proposal, not a replacement proof.** The 2026-09-20 manuscript
in the linked artifact formulates `compact-core-singfix-finiteness`
for all relevant finite marked sets and all finite-forest restrictions,
including the entire depth-zero base isotropy. That lemma remains OPEN.
The present route checks finite presentation via the cases explicitly
written below; its final higher-finiteness remark is still a remark,
not a completed proof of the stronger new theorem.

**0. The pieces.**
- *Generators are local.* `ĝ` preserves every `A_n` and every `0^n C`, is supported in
  `0C`, and is `V`-local off `p`. So `Ĝ` normalizes each `B_n`. `g ↦ ĝ` is an injective
  homomorphism, by separation.
- *Zoom.* `τ_p ∈ V` is `00w ↦ 000w`, `010w ↦ 001w`, `011w ↦ 01w`, and the identity on `1C`.
  So `τ_p α_n = α_(n+1)` for `n >= 2`, `τ_p(0^k C) = 0^(k+1) C` for `k >= 2`, and
  `τ_p^(-1) B_n τ_p = B_(n-1)` for `n >= 3`.
- *Ascending relation.* On `A_n`, `n >= 2`, `τ_p^(-1) ĝ τ_p` acts by
  `ρ_n(g) = ρ_(n-1)(φ(g))`, which is how `φ(g)^` acts. On `A_1`, `τ_p` maps `A_1` onto
  `A_1 ⊔ A_2`, and `ĝ` preserves both, so the conjugate preserves `A_1` and is `V`-local.
  On `A_0` both are the identity. So `τ_p^(-1) ĝ τ_p = φ(g)^ k_g` with `k_g ∈ V(01C)`.
- *Germ group.* By the trajectory argument of `rf-free-product-germ-realization-proof`,
  `(Γ)_p = <(Ĝ)_p, t>`, with `t^(-1) (ĝ)_p t = (φ(g)^)_p`.
  - The base elements `t^j g t^(-j)` act on deep `A_n` by `ρ_(n-j-1)(g)`, which is trivial
    for all large `n` only if `g = 1`.
  - `t`-exponents are additive.
  - So `(Γ)_p ≅ G *_φ`, the ascending HNN extension.
- *Finite germ extension.* Conditions 1--3 hold as in
  `prefix-replacement-actions-recode-into-germ-extensions-of-v`, and `sing(Γ) = V·p`.
- *Transitivity.* `V` is 2-transitive on `V·p`: `V_p ⊇ B_n` acts transitively on the
  eventually-zero points outside `0^n C`. So the Theorem 2.1 orbit condition holds for
  `n = 2`, and each SingFix type below needs checking at one pair only.

**Lemma (ascending HNN recognition).** Let `X = <P, s>` with `s^(-1) P s ⊆ P`, and suppose
`s^j ∉ ⋃_k s^k P s^(-k)` for `j != 0`. Then `X ≅ P *_ψ` with `ψ(x) = s^(-1) x s`.
- The union `U = ⋃_k s^k P s^(-k)` is normalized by `s` and contains `P`, so
  `X = U x| <s>`.
- The abstract `P *_ψ` is `(lim P) x| Z`. The natural map is injective on the directed
  union, because each stage maps isomorphically.
- If `P` has type `F_n`, so does `P *_ψ`: it is a graph of groups with vertex group `P`
  and edge group `ψ(P) ≅ P`.

**1. `SingFix({p},{p}) =: S_p`.**
- Put `P = B_3 x| Ĝ`, which has type `F_n` when `G` does, since `B_3 ≅ V_(2,3)` has type
  `F_∞`.
- `τ_p^(-1) P τ_p = B_2 · <φ(g)^ k_g> ⊆ P`, because `B_2` and `V(01C)` lie in `B_3`.
- Every `f ∈ S_p` has its germ realized by some `x ∈ <Ĝ, τ_p>`. Then `f x^(-1)` has no
  singular points and is trivial near `p`, so it lies in `K_p = ⋃_k τ_p^k B_3 τ_p^(-k)`.
  Hence `S_p = <P, τ_p>`.
- Germs of `U` have `t`-exponent 0, so the Lemma gives `S_p ≅ P *_ψ`, of type `F_n`.

**2. `SingFix({p},{p,q})`, with `q = 1 0^∞`.**
- `Ĝ` and `τ_p` are the identity on `1C ∋ q`, and `k_g ∈ V(01C)` fixes `q`.
- The same argument, with `P_q = Stab_(B_3)(q) x| Ĝ`, gives `Stab_(S_p)(q) ≅ P_q *_ψ`.
- `Stab_(B_3)(q)`, a point stabilizer in `V_(2,3)` at a rational point, has type `F_∞`.
- Every other pair `(a, b)` is `V`-conjugate to `(p, q)`.

**3. `SingFix({p,q},{p,q})`.**
- Let `v ∈ V` swap `0C` and `10C` and fix `11C`, so `v(p) = q` and `v(q) = p`. Put
  `Ĝ^q = v Ĝ v^(-1)` and `τ_q = v τ_p v^(-1)`.
- `Ĝ` and `τ_p` are supported in `0C`, and `Ĝ^q` and `τ_q` in `10C`, so they commute.
- `B^(2)_3 = V(C ∖ (000C ∪ 1000C))` is `v`-invariant and normalized by `Ĝ` and `Ĝ^q`. Put
  `P_2 = B^(2)_3 x| (Ĝ × Ĝ^q)`, of type `F_n`.
- `τ_p^(-1) P_2 τ_p ⊆ P_2`, because `τ_p^(-1)(000C) = 00C`, `τ_p` is the identity on `1C`,
  and `k_g ∈ V(01C) ⊆ B^(2)_3`. Symmetrically `τ_q^(-1) P_2 τ_q ⊆ P_2`.
- `E_1 = <P_2, τ_p>` is an ascending HNN extension, by exponents of germs at `p`.
  `τ_q^(-1) E_1 τ_q ⊆ E_1`, and `E_2 = <E_1, τ_q>` is ascending over `E_1`, by exponents of
  germs at `q`. Both have type `F_n`.
- `E_2 = SingFix({p,q},{p,q})`. Realize the germ pair of `f` by `xy`, with
  `x ∈ <Ĝ, τ_p>` and `y ∈ <Ĝ^q, τ_q>`, which have trivial germs at `q` and at `p`
  respectively. Then `f (xy)^(-1)` lies in `RStab_V({p,q}) = ⋃ τ_p^a τ_q^b B^(2)_3 τ_q^(-b) τ_p^(-a)`.

**4. The remaining groups.** `SingFix(∅,∅) = V`, `Fix_V(a)` and `Fix_V({a,b})` have type
`F_∞`, by the `V_(d,r)` stabilizer import in `germ-complex-and-bux-gonzalez-morse-inputs`,
transported by the bit flip `0 <-> 1`.

**5. Conclusion.**
- Theorem 2.1 with `n = 2` makes `Γ` finitely presented.
- `Γ` is full: a `Γ`-local homeomorphism agrees piecewise with finitely many elements, so
  it has finitely many singular points and germs in the groupoid.
- `Γ` is clopen transitive, because it contains `V`.
- The type (A) criterion then puts `Γ`, and so `Ĝ ≅ G`, in `B_A`.

**Remark (not written out).** With `k` points and `k` commuting zooms, the same
iterated-ascending argument should give type `F_n` for `Γ` when `G` has type `F_n`.
