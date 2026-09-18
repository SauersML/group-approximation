---
rg: 2
id: jacobson-haar-relation-laurent-affine-proof
kind: route
title: Pair finitely supported vectors with Laurent series by residues, read Toeplitz operators as truncated multiplications, and push sofic approximations of the relation through the full group
target: jacobson-haar-relation-is-laurent-affine-restriction
requires:
  - leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity
  - cordeiro-sofic-relation-permanence
  - ce-relation-full-group-subgroups-are-hyperlinear
---

## Step 0. Conventions and imported facts

* `J`, `n >= 2`, `E = EL_n(J)`, `V_+`, and `L = GL_fin(N x {1..n}, F_2)` are as in
  `leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity`.
  * Its proof, Step 2 (as quoted in Step 0 of `jacobson-el-characters-are-symbol-or-finitary-extensions-proof`), gives
    **(S1) `L <= E`**.
  * The convention is `e_ij = S^i Q T^j`, `e_ij e_j = e_i`. So `S e_k = e_(k+1)`, `T e_k = e_(k-1)` and `T e_0 = 0`.
* **Polynomial picture.** Identify `V_+` with `F_2[x]^n` by `e_k ⊗ ε_i <-> x^k ε_i`, where `ε_i` is the standard
  basis of `F_2^n`. For a Laurent series `f`, write `P_+ f` for its part of degree `>= 0` and `P_- f` for its part of
  degree `<= -1`. Then `S p = x p` and `T p = P_+(x^(-1) p)`.
* **Symbol.** The ring map `J -> A = F_2[x, x^(-1)]`, `S -> x`, `T -> x^(-1)`, is well defined, since `x^(-1) x = 1`.
  It induces `b -> b̄` on `M_n` and a group homomorphism `E -> EL_n(A)`, `g -> ḡ`. This map is onto: `x_ij(r̄)`
  lifts to `x_ij(r)` for any preimage `r in J` of `r̄`, and `J -> A` is onto.
* **Cordeiro.** `cordeiro-sofic-relation-permanence`, verbatim in Section 0 of
  `research/artifacts/paunescu-class-measure-equivalence-2026-09-12.md`:
  * Definition 2.1 (Ozawa): *"R is sofic if for each finite subset K ⊆ [[R]] and each ε > 0, there exists N ∈ ℕ and
    π : [[R]] → [[N]] satisfying: (i) π(id_X) = 1_[N]; π(∅) = ∅; (ii) For all φ, ψ ∈ K,
    d_#(π(φψ), π(φ)π(ψ)) < ε; (iii) For all φ ∈ K, |μ({x : φ(x) = x}) − μ_#({m : π(φ)(m) = m})| < ε."*
  * The proof of Theorem 2.2 records
    `d_μ(f,g) = tr(1_dom f) + tr(1_dom g) − tr(1_dom f 1_dom g) − tr(f^{-1} g 1_dom f)`.

    For partial bijections `f, h` of `[N]` with the uniform probability `μ_#`, the four terms count, in order:
    - `dom f`;
    - `dom h`;
    - `dom f ∩ dom h`;
    - the points `m in dom f ∩ dom h` with `f(m) = h(m)`.

    Hence

```text
d_#(f,h) = (1/N) |Dis(f,h)|,   Dis(f,h) = (dom f ∪ dom h) \ {m in dom f ∩ dom h : f(m) = h(m)}.     (0.1)
```

  * So `d_#` is symmetric. It satisfies the triangle inequality, since `Dis(f,k) ⊆ Dis(f,h) ∪ Dis(h,k)`. On
    permutations it is the normalized Hamming distance `d_H`.
* **Full group.** `ce-relation-full-group-subgroups-are-hyperlinear` (ESTABLISHED): *"If `L(R)` is Connes-embeddable,
  then every countable subgroup of `[R]` is hyperlinear."*
* **Soficity of a group** (the standard definition, e.g. Pestov's survey): for every finite `F ⊆ G` and `δ > 0` there
  are `N` and `σ : G -> Sym(N)` with the following two properties.
  - For all `g, h in F`, `d_H(σ(gh), σ(g)σ(h)) < δ`.
  - For all distinct `g, h in F`, `d_H(σ(g), σ(h)) > 1 - δ`.

## Step 1. The residue pairing

For `y in K^n` and `p in A^n` put `<y, p> = Res(y^T p)`, the coefficient of `x^(-1)` in `sum_i y_i p_i`. This is a
finite sum: `y_i` has only finitely many terms of positive degree, and `p_i` has only finitely many terms. The pairing
is `F_2`-bilinear, and for `a in M_n(A)`

```text
<y, a p> = <a^T y, p>.                                                              (1.1)
```

**(P1)** If `y in F_2[x]^n` and `p in F_2[x]^n`, then `<y, p> = 0`, since `y^T p` has no negative powers. Hence for
`p in F_2[x]^n`, `<y, p> = <P_- y, p>`.

**(P2)** For `y = sum_(k>=0) y_k x^(-k-1) in D` (`y_k in F_2^n`) and `p = sum_k p_k x^k in F_2[x]^n`,
`<y, p> = sum_k y_k . p_k`. So `ξ : D -> X_+ = Hom(F_2[x]^n, F_2)`, `ξ_y = <y, .>`, sends `y` to the functional with
coordinates `ξ_y(x^k ε_i) = (y_k)_i`.
* In coordinates, `ξ` is the identity map `(F_2^n)^N -> (F_2^n)^N`.
* It is an isomorphism of compact groups, from the `x^(-1)`-adic topology to the product topology.
* It carries the normalized Haar measure `m|_D` to `mu`, since both are the product of uniform measures.

**(P3)** Put `D_fin = D ∩ A^n = x^(-1) F_2[x^(-1)]^n`. Then `ξ(D_fin)` is the set of functionals vanishing on some
`x^M F_2[x]^n`, i.e. those with finitely many nonzero coordinates. It is countable, hence `mu`-null.

## Step 2. Toeplitz operators are truncated multiplications up to finite corrections

**Lemma 2.1.** For every `b in M_n(J)` there are `M >= 0` and an `F_2`-linear `F_b : F_2[x]^n -> F_2[x]^n` such that
the following hold.
* `F_b` vanishes on `x^M F_2[x]^n`.
* For all `p in F_2[x]^n`,

```text
b p = P_+(b̄ p) + F_b p.                                                              (2.1)
```

*Proof.* Since `TS = 1`, every word in `S, T` equals some `S^a T^c`, so `J` is spanned by these monomials. Both sides
of (2.1) are additive in `b`, and entrywise in the matrix. So it suffices to take `b = S^a T^c` acting on `F_2[x]`. Then:
* `b p = x^a P_+(x^(-c) p)` and `b̄ = x^(a-c)`.
* `x^(a-c) p = x^a P_+(x^(-c) p) + x^a P_-(x^(-c) p)`, and the first summand is a polynomial.
* Hence `P_+(b̄ p) = b p + P_+(x^a P_-(x^(-c) p))`.

Put `F_b p = P_+(x^a P_-(x^(-c) p))`, which in characteristic 2 is (2.1). The series `P_-(x^(-c) p)` depends only on
the coefficients `p_0, ..., p_(c-1)`, so `F_b` vanishes on `x^c F_2[x]`. For a sum of monomials, take the largest `M`
that occurs. `□`

**Lemma 2.2 (the dual action).** Let `g in E` and `y in D`. Then `ξ_y o g = ξ_(y')` for a unique `y' in D`, and

```text
y' ≡ ḡ^T y   (mod A^n).                                                             (2.2)
```

Moreover `y in D_fin` if and only if `y' in D_fin`.

*Proof.* Let `p in F_2[x]^n`. By (2.1), `ξ_y(g p) = <y, P_+(ḡ p)> + <y, F_g p>`.

For the first term, `<y, P_+(ḡ p)> = <y, ḡ p> + <y, P_-(ḡ p)>`. Here `y` and `P_-(ḡ p)` have all degrees `<= -1`, so
their product has all degrees `<= -2` and the second pairing is `0`. By (1.1) and (P1),
`<y, ḡ p> = <ḡ^T y, p> = <P_-(ḡ^T y), p>`.

For the second term, `p -> <y, F_g p>` is a functional vanishing on `x^M F_2[x]^n`. By (P2) and (P3) it equals `ξ_d`
for a unique `d in D_fin`.

So `ξ_y o g = ξ_(y')` with `y' = P_-(ḡ^T y) + d`. Uniqueness is (P2). Now `ḡ^T y - P_-(ḡ^T y) = P_+(ḡ^T y)` is a
polynomial vector, and `d in D_fin ⊆ A^n`, which gives (2.2).

If `y in D_fin ⊆ A^n`, then `ḡ^T y in A^n`, so `y' in A^n ∩ D = D_fin`. Applying this to `g^(-1)` and `y'` gives the
converse, since `ξ_(y') o g^(-1) = ξ_y`. `□`

## Step 3. Identification of the relations (Theorem, part 1)

Let `D' = D \ D_fin`. It is conull by (P3).
* `D'` is `R_Γ|_D`-saturated. If `y in D` and `(w, a).y in D`, then `y in A^n` if and only if `a y + w in A^n`.
* `ξ(D')` is `E`-invariant, by the last sentence of Lemma 2.2.

The orbit relation of `g.xi = xi o g^(-1)` is also generated by the maps `xi -> xi o g` (`g in E`). So it suffices to
show, for `y, y' in D'`, that

```text
ξ_(y') = ξ_y o g  for some g in E     <=>     y' = a y + w  for some a in EL_n(A), w in A^n.
```

**(=>)** This is (2.2) with `a = ḡ^T`. This `a` lies in `EL_n(A)` because `x_ij(r)^T = x_ji(r)`.

**(<=)** Let `y' = a y + w`. Transposes of elementary matrices are elementary, and `E -> EL_n(A)` is onto (Step 0), so
some `g in E` has `ḡ^T = a`.
* By Lemma 2.2, `ξ_y o g = ξ_(y'')` with `y'' ≡ a y ≡ y'` (mod `A^n`).
* Hence `d := y' + y'' in D ∩ A^n = D_fin`, so `d = sum_k d_k x^(-k-1)` has only finitely many `d_k != 0`.

It remains to find `h in E` with `ξ_(y'') o h = ξ_(y')`.
* Since `y'' in D'` has infinitely many nonzero coordinates, there are `k` and `i` with `d_k = 0` and
  `ξ_(y'')(e) = 1`, where `e = x^k ε_i`. Then `<d, e> = (d_k)_i = 0`.
* Put `h(p) = p + <d, p> e` on `V_+`. The functional `<d, .>` reads finitely many coordinates, so `h - 1` has finitely
  many nonzero matrix entries.
* `h^2(p) = p + <d,p> e + <d,p> e + <d,p><d,e> e = p`, so `h` is invertible.
* So `h in GL_fin(N x {1..n}, F_2) = L <= E` by (S1).

Then `ξ_(y'')(h p) = ξ_(y'')(p) + <d, p> ξ_(y'')(e) = <y'' + d, p> = <y', p>`. Thus `ξ_(y'') o h = ξ_(y')`, and hence
`ξ_(y') = ξ_y o (g h)`.

Together with (P2) this proves part 1. The restriction of `ξ` to `D'` is a measure-preserving isomorphism onto the
conull `E`-invariant set `ξ(D')`, and it carries `R_Γ|_(D')` onto `R_E|_(ξ(D'))`. `□`

## Step 4. The model is free, measure preserving and residually finite (Theorem, part 2)

**Measure.** `EL_n(A)` is generated by the shears `x_ij(r)`, which act on `K^n` by `y -> y + r y_j ε_i`. A shear
preserves the product Haar measure `m` by Fubini, and so does a translation.

**Freeness.** Let `γ = (w, a) != 1`, so `Fix(γ) = {y : (a + 1) y = w}`.
* If `a = 1`, then `w != 0` and `Fix(γ)` is empty.
* If `a != 1`, then `Fix(γ)` is empty or a translate of `ker_K(a + 1)`. That kernel is a proper `K`-subspace, so it
  lies in `{λ = 0}` for a nonzero `K`-linear functional `λ`. Complete `λ` to a coordinate system; the change of
  coordinates is in `GL_n(K)` and preserves null sets. In the new coordinates the set is `K^(n-1) x {0}`, which is
  null because `m({0}) = 0` on `K`.

**Linearity.** `(w, a) -> [[a, w], [0, 1]]` embeds `Γ_n` in `SL_(n+1)(A)`. Finitely generated linear groups are
residually finite (Mal'cev).

**Finite generation for `n >= 3`.**
* For distinct `i, j, k`, `x_ij(rs) = [x_ik(r), x_kj(s)]`, and `A` is generated as a ring by `x` and `x^(-1)`. So
  `EL_n(A)` is generated by the `x_ij(1)`, `x_ij(x)` and `x_ij(x^(-1))`.
* Conjugating `ε_1` by `x_j1(r)` gives `ε_1 + r ε_j`. So `A^n` is the normal closure of `ε_1`. `□`

## Step 5. Sofic transfer (Theorem, part 3)

Write `R = R_E` on `(X_+, mu)`. By part 1 and Cordeiro 3.2(a) (restriction to the conull set `ξ(D')` changes nothing),
`R` is sofic if `R_Γ|_D` is. For `g in E` let `α_g in [R]` be `xi -> xi o g^(-1)`. Then `g -> α_g` is a homomorphism
`E -> [R] ⊆ [[R]]`.

**(5.1) Uniform fixed-point bound.** For `g != 1`,

```text
mu(Fix α_g) <= 1/2.
```

`Fix α_g` is the annihilator of `im(g^(-1) - 1) != 0`, a proper closed subgroup `H` of `X_+`. If `H` has finite index
`i >= 2`, then `mu(H) = 1/i`. Otherwise `mu(H) = 0`. In particular `α` is injective.

**(5.2) From partial to full permutations.** Fix a finite symmetric `F_0 ⊆ E` with `1 in F_0`, and `0 < ε < 1/16`.
Let `F_1 = F_0 F_0`, which is symmetric, and `K = α(F_1)`. Take `π` from Cordeiro's Definition 2.1 for `(K, ε)`, and
write `f_g = π(α_g)`.

1. *Large domains.* Let `g in F_1`. Then `α_(g^(-1)) α_g = id`, and `π(id) = 1_[N]` by (i). By (ii),
   `d_#(1_[N], f_(g^(-1)) f_g) < ε`. By (0.1), `|[N] \ dom f_g| <= |[N] \ dom(f_(g^(-1)) f_g)| < εN`.
2. *Extension.* Extend `f_g` to a permutation `σ(g)` of `[N]`. This is possible since `|[N] \ dom| = |[N] \ ran|`. By
   (0.1), `d_#(σ(g), f_g) < ε`. For `g notin F_1` let `σ(g) = 1`.
3. *Multiplicativity on `F_0`.* Let `g, h in F_0`, so `gh in F_1`. The points `m in Dis(σ(g)σ(h), f_g f_h)` satisfy
   `m notin dom f_h` or `f_h(m) notin dom f_g`. Since `f_h` is injective there are fewer than `2εN` of them. By (ii)
   and the triangle inequality,

```text
d_H(σ(gh), σ(g)σ(h)) <= d_#(σ(gh), f_gh) + d_#(f_gh, f_g f_h) + d_#(f_g f_h, σ(g)σ(h)) < 4ε.     (5.2)
```

4. *Few fixed points.* Let `g in F_1 \ {1}`. A fixed point of `σ(g)` lying in `dom f_g` is a fixed point of `f_g`. So
   by (iii) and (5.1),

```text
(1/N)|Fix σ(g)| < μ_#(Fix f_g) + ε < mu(Fix α_g) + 2ε <= 1/2 + 2ε <= 5/8.             (5.3)
```

**(5.3) Amplification.** For `r >= 1` let `σ_r(g) = σ(g)^(x r)` act coordinatewise on `[N]^r`.
* A tuple is fixed by `σ_r(g)` exactly when every coordinate is fixed by `σ(g)`. So for `g in F_1 \ {1}`, the fixed
  fraction of `σ_r(g)` is less than `(5/8)^r`.
* A tuple lies in `Dis(σ_r(gh), σ_r(g)σ_r(h))` only if some coordinate lies in `Dis(σ(gh), σ(g)σ(h))`. So
  `d_H(σ_r(gh), σ_r(g)σ_r(h)) < 4rε` for `g, h in F_0`.

**(5.4) Separation of distinct elements.** Let `g != h` in `F_0`, so `u = h^(-1) g in F_1 \ {1}`. Each of the
following facts uses only `(5.2)` for pairs in `F_0`.
* Using `d_H(σ(1)σ(1), σ(1)) < 4ε`, we get `d_H(σ(1), 1) < 4ε`.
* Using `d_H(σ(h)σ(h^(-1)), σ(1)) < 4ε`, we get `d_H(σ(h)^(-1), σ(h^(-1))) < 8ε`.
* Using `d_H(σ(h^(-1))σ(g), σ(u)) < 4ε`, together with the left and right invariance of `d_H`, we get

```text
d_H(σ(g), σ(h)) = d_H(σ(h)^(-1)σ(g), 1) >= d_H(σ(u), 1) - 12ε > 1 - 5/8 - 12ε.
```

The same estimates hold for `σ_r` with `4ε` replaced by `4rε`. That gives
`d_H(σ_r(g), σ_r(h)) > 1 - (5/8)^r - 12rε`.

**(5.5) Conclusion.** Given a finite `F ⊆ E` and `δ > 0`:
* let `F_0 = F ∪ F^(-1) ∪ {1}`;
* choose `r` with `(5/8)^r < δ/2`;
* then choose `ε < min(1/16, δ/(24r))`.

Then `σ_r : E -> Sym(N^r)` satisfies:
* `d_H(σ_r(gh), σ_r(g)σ_r(h)) < δ` for `g, h in F`;
* `d_H(σ_r(g), σ_r(h)) > 1 - δ` for distinct `g, h in F`.

So `E` is sofic. `□`

## Step 6. CE transfer (Theorem, part 4)

Suppose `L(R_Γ|_D)` is Connes-embeddable. By part 1, `L(R_E)` is isomorphic to it, since the relations agree off a
null set. By `ce-relation-full-group-subgroups-are-hyperlinear`, the countable subgroup `α(E)` of `[R_E]` is
hyperlinear. By (5.1) `α` is injective, so `E` is hyperlinear.

For the character, the dictionary of that node gives `tau_R(u_(α_g)) = mu(Fix α_g)`. By (JH2) of
`leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity` this is `phi_1(g)`. So `phi_1` is the restriction of
the trace of the CE algebra `L(R_E)` along the unitary representation `g -> u_(α_g)`, and it is therefore CE. `□`

## Step 7. What is not proved

* Whether `R_Γ|_D` is sofic, or whether its von Neumann algebra is CE, is open. The two half-relations described in
  the claim are the natural approximable pieces, and they are only sketched there.
* No converse is claimed. Soficity of `E` is not shown to imply soficity of `R_Γ|_D`, since `E` acts non-freely and
  the relation also sees the Haar measure.
* Nothing here uses `n >= 3` except finite generation of `Γ_n` in part 2.
