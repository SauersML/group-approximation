---
rg: 2
id: commuting-subshift-automorphisms-space-time-rf-proof
kind: route
title: Rows of a legal periodic space-time configuration obey the block code, uniform recurrence gives covering, and the Z^2 crossed product makes the automorphism inner
target: commuting-subshift-automorphisms-die-when-space-time-is-rf
requires:
  - rf-subshifts-are-periodic-window-approximable
  - window-lef-subshifts-give-matricial-crossed-products
  - virtually-inner-ring-automorphisms-fail-centralizer-compression
  - minimal-subshift-algebra-is-simple-lef-ring
---

## Why sufficient

Notation as in the target.  `Z^2` acts on patterns by `(g·c)(h) = c(h-g)`.  For a finite `W ⊆ Z^2`,
`L_W(Y)` is the set of restrictions `y|_W`, and `X_W(Y)` is the window SFT of
`rf-subshifts-are-periodic-window-approximable`.  Boxes are `B(M,H) = [0,M) × [0,H)`.

### Step 0: Y_ψ is a perfect Z^2 subshift conjugate to (X, ⟨T,ψ⟩)

- `Φ` is continuous, since each coordinate `(ψ^n x)_m` depends continuously on `x`.
- `Φ` is injective, because row `0` of `Φ(x)` is `x`.
- It intertwines the actions:
  `Φ(Tx)(m,n) = (ψ^n x)_(m+1) = Φ(x)(m+1,n)` and `Φ(ψx)(m,n) = Φ(x)(m,n+1)`.
  Hence `Φ(T^a ψ^b x) = (-(a,b))·Φ(x)`.
- So `Y_ψ = Φ(X)` is closed and invariant, and `Φ` is a homeomorphism `X -> Y_ψ`.
  In particular `Y_ψ` has no isolated points, because `X` is infinite and minimal.
- Kerr–Nowak residual finiteness is invariant under conjugacy.  It is also invariant under
  reparametrizing the acting group by an automorphism: twist the finite model's `Γ`-set by the same
  automorphism, and the approximation conditions over finite `F ⊆ Γ` are permuted.
- So (a) is equivalent to Kerr–Nowak residual finiteness of `Y_ψ`.
- By `window-lef-subshifts-give-matricial-crossed-products`, item 4, that is equivalent to (b), since `Z^2` is
  finitely presented.

### Step 1: boxes suffice in the window criterion

By `rf-subshifts-are-periodic-window-approximable`, `Y_ψ` is residually finite iff, for every finite `W`, some
finite invariant `O ⊆ X_W(Y_ψ)` satisfies `{c|_W : c ∈ O} = L_W(Y_ψ)`.

Two facts reduce this to boxes.
- `X_(W+g) = X_W` for every translate.
- If `W ⊆ W'` then `X_(W') ⊆ X_W`, and `L_W` consists of the restrictions of `L_(W')`.
  So a covering orbit set for `W'` is one for `W`.

Every finite `W` lies in a translate of some `B(M,H)`, so it suffices to treat boxes, and large ones.

### Step 2: legal configurations obey the block code

Let `M ≥ 2ρ+1`, `H ≥ 2`, and `c ∈ X_(B(M,H))(Y_ψ)`.  Then for all `(m,n)`:

```text
c(m,n+1) = f(c(m-ρ,n), ..., c(m+ρ,n)).
```

The translate of `B(M,H)` whose bottom-left corner is `(m-ρ,n)` contains the cells `(m-ρ..m+ρ, n)` and
`(m, n+1)`.  By definition of `X_W`, `c` agrees there with a translate of some `Φ(x)`.  In `Φ(x)` the displayed
identity holds, because `ψ^(n+1) x = F(ψ^n x)`.

So the rows `c_n = c(·,n) ∈ A^Z` satisfy `c_(n+1) = F(c_n)`.

### Step 3: (a) implies (c)

- Fix `M` and put `M_1 = max(M, 2ρ+1)`.  Take the box `B = B(M_1, 2)` and the finite invariant covering set
  `O ⊆ X_B(Y_ψ)` of Step 1.  `O` is nonempty because `L_B(Y_ψ)` is nonempty.
- Pick `c ∈ O`.  Its orbit is finite, so its stabilizer has finite index in `Z^2` and contains some `(p,0)`
  with `p ≥ 1`.  Then `y = c_0` is `p`-periodic.
- By Step 2, `c_j = F^j(y)` for every `j ≥ 0`.
- A length-`M` subword of `c_j` at position `a` lies inside the bottom row of the `B`-pattern of `c` at `(a,j)`.
  That pattern is a pattern of some `Φ(x)`, whose rows are points `ψ^n x ∈ X`.
- So the subword lies in `L_M(X)`.  This is `(*)_F`.

### Step 4: (c) implies (a), for any block code F of ψ

Fix a box `B = B(M,H)` with `M ≥ 2ρ+1` and `H ≥ 2`, and put `M' = M + 2ρ(H-1)`.

**Choosing M''.**  `X` is minimal, hence uniformly recurrent.  So there is `M''` such that every word of
`L_(M'')(X)` contains every word of `L_(M')(X)`.

**The periodic configuration.**
- Apply `(*)_F` with `M''` to get a `p`-periodic `y` all of whose iterates `F^j(y)`, `j ≥ 0`, are
  `M''`-legal.
- `F` commutes with the shift, so it maps the finite set of `p`-periodic sequences to itself.  Hence
  `F^(j_0+L)(y) = F^(j_0)(y)` for some `j_0 ≥ 0` and `L ≥ 1`.
- Put `y' = F^(j_0)(y)`.  Define `c` by `c_n = F^(n mod L)(y')`, so that `c_(n+1) = F(c_n)` for all `n ∈ Z`.
- `c` is fixed by `(p,0)` and `(0,L)`, so its `Z^2`-orbit `O` is finite.
- Every row of `c` is some `F^j(y)` with `j ≥ j_0`, so every row is `M''`-legal and hence `M'`-legal.

**Legality: c ∈ X_B(Y_ψ).**
- Fix a position `(a,b)`.  Put `I = [a-ρ(H-1), a+M+ρ(H-1))`, of length `M'`.
- `u = c_b|_I` is a word of `X`.  So some `x ∈ X` has `x|_I = u`, because `L(X)` is shift invariant.
- For `0 ≤ h < H`, both `c_(b+h)|_([a,a+M)) = F^h(c_b)|_([a,a+M))` and `(ψ^h x)|_([a,a+M)) = F^h(x)|_([a,a+M))`
  depend only on the restriction to `[a-ρh, a+M+ρh) ⊆ I`, where the two sequences agree.
- So the `B`-pattern of `c` at `(a,b)` equals the `B`-pattern of `Φ(x)` at `(a,0)`, which lies in
  `L_B(Y_ψ)`.
- Hence `c ∈ X_B(Y_ψ)`, and so is its whole orbit `O`.

**Covering.**
- Let `P ∈ L_B(Y_ψ)`.  By invariance, `P` is the `B`-pattern at `(0,0)` of some `Φ(x)`.
- By the argument above, `P` is determined by the word `u = x|_([-ρ(H-1), M+ρ(H-1)))`, which lies in `L_(M')(X)`.
- The row `c_0` contains a word of `L_(M'')(X)`, which contains `u` at some position `a - ρ(H-1)`.
- The legality computation, applied at `(a,0)`, shows that the `B`-pattern of `c` at `(a,0)` is `P`.
- So `O` realizes all of `L_B(Y_ψ)`.

By Step 1, `Y_ψ` is residually finite, and Step 0 gives (a).  Condition (a) does not mention `F`, so `(*)`
for one block code gives it for all.  This proves Theorem 1.

### Step 5: Theorem 2 (the Z^2 crossed product implements σ_ψ)

Conventions: `u f u^(-1) = f ∘ T^(-1)` in `S`, as in `minimal-subshift-algebra-is-simple-lef-ring`.

**Case 1: ψ of finite order modulo ⟨T⟩.**  This case is already in
`subshift-diagonal-automorphisms-need-infinite-spatial-class`; here is the direct argument.
- Say `ψ^r = T^s` with `r ≥ 1`.  Then `σ_ψ^r = Ad(u^s)` on `S`.
- Since `σ_ψ^k ∘ Ad(w) = Ad(σ_ψ^k(w)) ∘ σ_ψ^k`, the power `σ^(mr) = (Ad(w) σ_ψ^k)^r` is `Ad(w_r) σ_ψ^(kr)`, where
  `w_r = w σ_ψ^k(w) ... σ_ψ^(k(r-1))(w)`.
- That equals `Ad(w_r u^(sk))`, which is inner in `S`.
- `S` embeds in an ultraproduct of matrix algebras by `minimal-subshift-algebra-is-simple-lef-ring`, item 3.
  So `virtually-inner-ring-automorphisms-fail-centralizer-compression` applies with overring `S` itself.

**Case 2: ψ of infinite order modulo ⟨T⟩.**

*Freeness.*
- Suppose `T^a ψ^b` fixes some point, with `(a,b) ≠ 0`.
- Its fixed-point set is closed and `T`-invariant, because `T` and `ψ` commute.  So by minimality it is all
  of `X`, i.e. `ψ^b = T^(-a)`.
- If `b = 0`, then `T^a = id` with `a ≠ 0`, which is impossible on an infinite minimal subshift.  If `b ≠ 0`,
  then `ψ` has finite order modulo `⟨T⟩`.
- So the `Z^2`-action `β_(a,b) = T^a ψ^b` is free, and `Y_ψ` is a free subshift.

*The overring.*
- Let `𝒯 = LC(X,F_q) ⋊_β Z^2`, with units `u_g` satisfying `u_g u_h = u_(g+h)` and
  `u_g f u_g^(-1) = f ∘ β_g^(-1)`.
- Transport by `Φ` identifies `𝒯` with `LC(Y_ψ,F_q) ⋊ Z^2`, up to the reparametrization `g ↦ -g`, which the
  isomorphism `u_g ↦ u_(-g)` absorbs.
- By (b) and `window-lef-subshifts-give-matricial-crossed-products`, item 2, `𝒯` embeds unitally and
  injectively in `∏_ω M_(N_n)(F_q)`.

*The embedding of S.*
- The rule `f ↦ f`, `u ↦ u_(1,0)` respects the defining relation, so it defines a ring map `S -> 𝒯`.
- The map is injective, because `{u_(n,0)}` is part of a free left `LC(X,F_q)`-basis of `𝒯`.

*σ_ψ becomes inner.*
- Put `v = u_(0,1)`.  Then `v f v^(-1) = f ∘ ψ^(-1) = σ_ψ(f)`.
- Also `v u_(1,0) v^(-1) = u_(1,0) = σ_ψ(u)`.
- So `σ_ψ = Ad(v)` on `S`, and `σ^m = Ad(w v^k)` on `S`, where `w v^k ∈ 𝒯^×`.
- `virtually-inner-ring-automorphisms-fail-centralizer-compression` now shows the following.  For every
  finitely generated unital `R ≤ S` with `σ(R) ⊆ R`, and every `z` commuting with `R`, the element `z` commutes
  with `σ^(-1)(R)`.  So `(G2)` fails.

### Step 6: Theorem 3 (product subshifts)

**Setup.**
- `X = X_1 × X_2 ⊆ (A_1 × A_2)^Z` is assumed minimal.  Its language is `L_M(X) = L_M(X_1) × L_M(X_2)`.
- `ψ = T_1 × id` commutes with `T = T_1 × T_2`.  It is a block code `F(y^1, y^2) = (T y^1, y^2)` of radius
  `1`.

**Infinite order.**
- Suppose `ψ^b = T^a`.  On the second factor this gives `T_2^a = id`, so `a = 0`, since `X_2` is infinite
  minimal.
- Then `T_1^b = id`, so `b = 0`.

**(*) holds.**
- *A periodic legal word in each factor.*  Fix `M`, and let `x ∈ X_i` and `w = x|_([0,M))`.
  - By minimality, `w` recurs in `x` at some position `p ≥ 1`, i.e. `x|_([p,p+M)) = w`.
  - Every length-`M` subword of the `p`-periodic sequence `y^i = (x|_([0,p)))^∞` is a subword of
    `x|_([0,p+M))`, so it is legal.
- *The product.*  Take `y = (y^1, y^2)`, which is `p_1 p_2`-periodic.
  - `F^j(y) = (T^j y^1, y^2)`.
  - Its length-`M` subwords are pairs of legal words, so they lie in `L_M(X)`.

**Existence of minimal products.**
- Take `X_1` the period-doubling subshift and `X_2` a Sturmian subshift of irrational slope `α`.
- These are almost one-to-one extensions `π_i` of the dyadic odometer `Z_2` and of the rotation `R_α` (recalled,
  standard).
- The rotation of `Z_2 × T` by `(1, α)` is minimal.  A character `(k/2^j, l)` trivial on it forces `lα ∈ Q`,
  so `l = 0`, and then the character is trivial.
- Let `K ⊆ X_1 × X_2` be closed, nonempty and invariant.
  - Then `(π_1 × π_2)(K)` is everything, so `K` contains every point whose two fibres are singletons.
  - In each `X_i`, the points with singleton fibre form a nonempty invariant set, so they are dense by
    minimality.
  - So such pairs are dense, and `K = X_1 × X_2`.

**Why this reaches genuine survivors.**  The spatial homeomorphism of `σ_ψ` is `ψ` itself.  Its class in
`N[[T]]/[[T]]` has infinite order, because `ψ^b ∈ [[T]]` would make `ψ^b` preserve `T`-orbits.  But `ψ^b` moves
the first coordinate along its `T_1`-orbit while fixing the second, and no power of `T` does that unless
`b = 0`, because the `T_2`-orbits are free.  So these are survivors of the spatial-class kill, and Theorem 2
disposes of them.

### Step 7: Theorem 4 (realization and the SFT obstruction)

**Setup.**
- Let `ℓ = Rv` be expansive for `Y'`: there is `r` such that `y|_(ℓ^r ∩ Z^2) = y''|_(ℓ^r ∩ Z^2)` implies
  `y = y''`, where `ℓ^r` is the closed `r`-neighbourhood of `ℓ`.
- Choose `g ∈ GL_2(Z)` with `g v = e_1`.  This is possible because `v` is primitive.
- Replace `Y'` by `{y ∘ g^(-1)}`.  This is conjugate, after the automorphism `g`, and transforms `ℓ^r` into a
  strip around `R e_1` contained in `Z × [-h, h]` for some `h`.

**The row subshift.**
- Let `X = {(y(m, -h..h))_(m ∈ Z) : y ∈ Y'} ⊆ (B^(2h+1))^Z`, with restriction map `ρ_h : Y' -> X`.
- `ρ_h` is continuous and surjective, intertwines `e_1` with `T`, and is injective by expansivity.  So it is a
  conjugacy.
- `ψ = ρ_h ∘ (e_2-shift) ∘ ρ_h^(-1)` is a homeomorphism commuting with `T`.
- `X` is `T`-minimal, because `e_1` acts minimally.
- `X` is infinite, and `ψ` has infinite order modulo `⟨T⟩`, because `Y'` is free.
- The `Z^2`-action `⟨T, ψ⟩` on `X` is conjugate to `Y'`.  By Step 0 it is conjugate to `Y_ψ`, up to the
  automorphism `-id`.

**The equivalence.**
- One direction: for every infinite-order `ψ`, `Y_ψ` is free (Step 5) and minimal.  Moreover `e_1` is an
  expansive direction, since row `0` determines the configuration, and it acts minimally, since `T` does.
- The other direction: every such `Y'` arises as above.
- Residual finiteness is invariant under conjugacy and reparametrization (Step 0).  This gives the stated
  equivalence.

**The SFT obstruction.**
- Let `Σ` be a `Z^2` SFT without periodic points, defined by forbidden patterns on a window `W_0`, and let
  `Y' ⊆ Σ` be minimal.
- For `W ⊇ W_0`, every `W_0`-pattern of a `c ∈ X_W(Y')` is a pattern of `Y' ⊆ Σ`.  So `X_W(Y') ⊆ Σ`, which has
  no finite orbits.
- A finite orbit is a set of periodic points, so no nonempty finite invariant `O ⊆ X_W(Y')` exists.
- So `Y'` is not residually finite by `rf-subshifts-are-periodic-window-approximable`.  Being minimal and
  infinite, `Y'` is perfect, so that criterion applies.
