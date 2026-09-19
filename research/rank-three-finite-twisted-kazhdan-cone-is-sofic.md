---
rg: 2
id: rank-three-finite-twisted-kazhdan-cone-is-sofic
kind: claim
title: The rank-three finite twisted Kazhdan cone, twisted by evaluation at the origin, is sofic
distinct_from:
  finite-twisted-kazhdan-cone-is-sofic: that asks the question for every rank r ≥ 3 and is refuted for r ≥ 5 by block subpairs; this is the rank-three case, where no 3-element block has a disjoint centralising element.
  block-subpairs-make-twisted-kazhdan-cones-nonsofic: that proves nonsoficity whenever a block subpair has a trace with nontrivial centraliser; this is the case where every block trace is all of Gamma.
---

**OPEN.**  Let `R_+ = F_q[x_1..x_d]` and `R = F_q[x_1^(±1)..x_d^(±1)]` with `d ≥ 3`.  Let
`Gamma = EL_3(R_+) ≤ G = EL_3(R) x| SL_d(Z)` be the rank-three Kun-Thom Theorem E pair.  Let
`psi : Gamma -> F = PSL_3(F_q)` be evaluation at the origin followed by projection.  Is

```text
T_3 = (F x Gamma) *_(Gamma_psi) G
```

sofic, for some prime power `q` and some `d ≥ 3`?  The companion case `r = 4`, `q ∈ {2, 3, 5}` of
[[finite-twisted-kazhdan-cone-is-sofic]] is equally open and would serve the same purpose.

**Why it matters.**  By [[block-subpairs-make-twisted-kazhdan-cones-nonsofic]], every twisted-diagonal cone
over a Theorem E pair of rank `r ≥ 5` is nonsofic, for every twist.  The same holds in rank four for
`q ∉ {2, 3, 5}`.  So the twisted-cone route of [[kazhdan-double-cones-add-one-sigma1-bit]] to
[[sofic-recognition-finite-presentations-is-pi2-complete]] survives only through these low-rank pairs.  By
[[twisted-diagonal-cones-need-a-profinitely-invisible-core]] it survives only through a twist with a
centreless invisible core, and `T_3` is the basic example.

**What is known.**
- `T_3` is not residually finite.
- Every finite-index level `G_1` has `psi(Gamma ∩ G_1) = F`, by (V5) of the invisible-core node.
- The only block subpair is `(G, Gamma)` itself, and `F` is centreless.

**What would decide it.**
- *Nonsofic.*  Find a subgroup `B ≤ G` with `C_F(psi(B ∩ Gamma)) ≠ 1` and `B *_(B ∩ Gamma) B` nonsofic.  Such a
  `B` must have infinite index and must not be normal.  If `B ∩ Gamma` has finite index in `Gamma`, for instance
  `ker ev_0`, then `B` must avoid most of the nonnegative compressors in `SL_d(Z)`, because `ker ev_0` and
  `SL_d(Z)` together generate `G`.  Relative groups `EL_3(R, I) x| Stab(I)` over ideals `I` vanishing at the
  origin are the candidates named in [[finite-twisted-kazhdan-cone-is-sofic]].
- *Sofic.*  Build sofic approximations of `T_3`.  They cannot come from finite quotients of `T_3`.  This would be the first soficity theorem for an
  amalgam over a Kun-Thom subgroup that is not a free factor.

## Attempts

- **w8-111r, 2026-09-18: hypersurface-level subpairs (obstruction).**
  - *Result.*  By [[divisor-level-subpairs-cannot-certify-rank-three-twisted-cone]], graded diagonal twists
    `B = D (EL_3(F_q[L]) x| H) D^-1` satisfy the centraliser condition.  Their origin image lies in the torus, and
    `B` is Kazhdan with `B ∩ Gamma` infranormal and not normal in `B`.  But `B ∩ Gamma` maps onto an infinite
    Borel subgroup over `F_q[x_2..x_d]`, so it is not Kazhdan.  The relative groups `EL_3(R, I) x| Stab(I)` fail
    too, for every ideal `I`: either `psi(B ∩ Gamma) = F`, or `B ∩ Gamma` has an infinite abelian quotient.
  - *Why.*  Both families shrink `psi(B ∩ Gamma)` by a level along a hypersurface, and that level becomes an
    infinite amenable quotient of the edge.
  - *What is left.*  A Kazhdan edge with a level only at the origin, such as `ker ev_0` or `ev_0^-1(Borel)`,
    inside a subgroup `B` that avoids the nonnegative compressors.  Or build sofic approximations.
  - *Graph.*  This node now feeds the route [[sofic-fp-completeness-from-rank-three-twisted-kazhdan-cones]].
- **w9-111, 2026-09-18: origin-level monomial subpairs (obstruction).**
  - *Result.*  By [[monomial-origin-level-subpairs-cannot-certify-rank-three-cone]], take
    `B = < U_k, H >` with `U_k` the monomial elementary matrices of degree `≥ k` and `H ≤ SL_d(Z)`.  Then
    `B = Ũ x| H` and `psi(B ∩ Gamma)` is `1` or `F`: it is `F` exactly when `cone(H · R_+^d)` contains a line.
    For every `B ⊇ U_k`, a line in `cone(H_B · R_+^d)` already forces `psi(C) = F`.  In the salient case
    with `H` infinite and pointed closure, `B` maps onto `F_q wr_X H` with `X` infinite, so it is not Kazhdan.
    The symmetric-square PSD candidate `Sym^2 SL_3(Z)` falls here.  With `H` finite, `C` is profinitely
    closed in `B`, so it cannot be infranormal and non-normal.
  - *Why.*  The exponent semigroup `P` grades `B ∩ EL_3(R)`.  Pointedness makes the grading discrete, and then
    the irreducibles of `P` give an infinite permutation-module quotient, or, for finite `H`, a degree
    filtration by finite-index normal subgroups.
  - *What is left.*  An infinite Kazhdan `H` whose cone `cone(H · R_+^d)` is salient but has a closure with a
    nonzero lineality space.  A test case is `Sym^2 SL_3(Z[√2])` on `Z^12`.  Also left: subgroups `B ⊇ U_k`
    that are not generated by `U_k` and monomial elements.
- **w10-111, 2026-09-18: Galois-twisted PSD candidate and the compressor lemma (obstruction).**
  - *Result.*  By [[galois-psd-monomial-subpair-has-no-infranormal-trace]], `H = Sym^2 SL_3(Z[√2])` on `Z^12`
    does realise the residual geometry: `K0` is salient, `K = PSD × Sym^2 R^3`, and the lineality space is the
    irrational `V_-`.  But for every `B_(H,k)` with salient `K0`, `C` is infranormal in `B` exactly when the
    nonnegative matrices `H ∩ M_d(N)` generate `H`.  For this `H` they form a group of order 6, so `C` is not
    infranormal and Theorem A never applies.  Property (T) of `Ũ` and `C` does not need to be decided.
  - *Why.*  A compressor `u σ` conjugates `e_ij(x^m)` to an element whose `(i, j)` entry has leading monomial
    `x^(σm)`, because `0 ∉ P`.  So `σ` must map the orthant into itself.  The orthant of `Sym_3(Z[√2])` is
    `{ X_+ ± X_- diagonally dominant }`, and that forces the columns of `g` to be integral.
  - *What is left.*  A monomial certificate needs an infinite Kazhdan `H ≤ SL_d(Z)` generated by nonnegative
    matrices, with `cone(H · R_+^d)` salient and non-pointed closure.  Deciding whether such an `H` exists
    settles every origin-level monomial subpair.  The kill is basis-dependent: `Sym^2 SL_3(Z[√2])` in a
    different lattice basis, whose simplicial cone some generating set of a finite-index subgroup preserves,
    would survive.  Otherwise the nonsofic side needs `B ⊇ U_k` with
    `B ∩ EL_3(R)` larger than `Ũ`.
- **w11-111, 2026-09-18: atoms of the exponent monoid (obstruction).**
  - *Result.*  By [[atomic-exponent-monoids-kill-monomial-kazhdan-subpairs]], the wreath quotient of (M3)
    needs only an infinite atom set `X` of the exponent monoid `P`, not a pointed closure.  So `B_(H,k)` with
    `H` infinite is not Kazhdan whenever `P` is atomic, and in particular whenever the lineality space `L` of
    `K` is rational and misses the orthant.  The (M5) geometry does occur with (T) over `Z`: `SL_3(Z)` on
    `Z^3 ⊕ Sym^2 Z^3` has `K0` salient and `K = R^3 × PSD`.  But its `L` is rational, so it dies.
  - *Why.*  A rational `L` gives an integral functional that is positive on `P`, through the pointed quotient
    `K / L`.  Atomicity then makes `X` span, and an infinite `H` then gives infinitely many atoms.
  - *What is left.*  A monomial certificate needs an infinite Kazhdan `H ≤ SL_d(Z)` with three properties:
    it is generated by nonnegative matrices, `K0` is salient, and `P` is non-atomic with a finite atom set.
    The last property holds only if `L` is irrational or meets the orthant.  The sharp open question: does
    nonnegative generation of a Kazhdan `H` force `P` to be atomic?
- **w12-111, 2026-09-18: Vinberg volume rigidity (obstruction).**
  - *Result.*  By [[kazhdan-volume-rigidity-kills-interior-orthant-subpairs]], take `H ≤ SL_d(Z)` with no
    nontrivial homomorphism to `R_(>0)^×`, for instance `H` Kazhdan, and with `L ∩ O = 0`.  Suppose also that
    the orthant has finite Vinberg volume `I(H) = ∫_Δ φ_(K/L)(π u)^(d/n) du`, which holds for instance when
    `π(O \ 0) ⊆ int(K/L)`.  Then every nonnegative element of `H` is a permutation matrix, so nonnegative
    generation forces `H` to be finite.  The same holds with no volume condition when `H` acts on `V/L`
    through a relatively compact group.  Lineality meeting the orthant splits `H` into a quotient piece, where
    these results apply, and a piece inside `L`.
  - *Why.*  `exp(-φ_Q(π x)^(-1/n)) dx` is an `H`-invariant measure: `φ_Q` transforms by `|det|` on `V/L`, and
    (T) kills that character.  When `I(H) < ∞` the orthant has finite mass, so a nonnegative `g` cannot map
    `O` strictly into itself.  The abelian example, `3 + 2√2` on `Z[√2]`, meets every hypothesis except the
    character condition, and it does compress `O`.
  - *What is left.*  The atomicity question is bypassed rather than answered.  Every origin-level monomial
    subpair with infinite Kazhdan `H` is dead except in two cases.  Either the piece of `H` on `R^J = span(L ∩ O)`
    is infinite, or the quotient piece acts non-compactly on `V/L` with an orthant that touches `∂(K/L)`,
    making the volume infinite.  For the PSD geometry this means some basis matrix is singular at the
    non-compact place.  The next step is to run the volume argument on the face stabilisers of `K/L`.
- **w13-111, 2026-09-18: face-graded Vinberg measure (class-killing obstruction).**
  - *Result.*  By [[nonneg-generated-kazhdan-groups-have-nonsalient-cones]], an infinite Kazhdan
    `H ≤ GL_d(Z)` generated by nonnegative matrices always has a line in `cone(H · R_+^d)`.  With (N1) and
    (M2)/(M4), this kills **every** origin-level monomial subpair `B_(H,k)`, in every lattice basis, with no
    condition on atoms, rationality of `L`, or the Vinberg volume.  It settles (N5) in the negative and makes
    the atomicity question moot.
  - *Why.*  Nonnegative elements permute the finitely many faces of `K/L` spanned by coordinate sets.  A
    finite-index subgroup fixes them all, and each nonnegative element of it is block triangular for the
    partition of indices by carrier face.  Each diagonal block is weighed with Vinberg's function of its own
    face, where its orthant is interior.  The cross terms only push deeper into the face, so the weight can
    only increase, and (T) kills the determinant character on the face.  So the blocks are permutations.  The
    unipotent remainder would put a vector of `O` in `L`.  Lineality meeting `O` is handled by recursion, which
    can end only with a coordinate subspace inside `K0`.
  - *What is left.*  The monomial nonsofic side is closed.  A nonsofic certificate needs `B ⊇ U_k` with
    `B ∩ EL_3(R)` strictly larger than `Ũ`, where (N1) is unproved, or a `B` containing no level `U_k`.
    Otherwise the sofic side: build approximations of `T_3`.
- **w14-111, 2026-09-18: compressors of every level-containing subpair (class-killing obstruction).**
  - *Review.*  The proof of (W1)/(W2) of [[nonneg-generated-kazhdan-groups-have-nonsalient-cones]] was checked
    adversarially at its two delicate steps, and no flaw was found.  In the block-triangular step, the cross term
    `π b` lies in `F`, and `π g_F y` lies in `relint F` because `g_F` is invertible.  So (Φ2) applies, and `φ_F`
    can only drop.  In the recursion, the quotient piece has `L'' ∩ O' = 0`: `K + R^J = K`, so the image of `K`
    is closed, and `-p(e_i) ∈ p(K)` would put `e_i` in `L ∩ O`.
  - *Result.*  By [[subring-level-subpairs-cannot-certify-rank-three-cone]], take any `B ≤ G` containing some
    `U_k`, and let `H_B` be its projection to `SL_d(Z)`.  Then every compressor of `C = B ∩ Gamma` projects to a
    nonnegative matrix; no salience or monomial hypothesis is needed.  If `H_B` is finite, an infranormal `C` is
    normal.  If `B ∩ EL_3(R) = EL_3(A)` for a subring `A`, then a line in `cone(H_B · R_+^d)` gives `1 ∈ A`, and
    so `psi(C) = F`.  With (W2), no such `B` is a Kun-Thom certificate.  This covers monomial subrings
    `F_q[P]`, and lifts `u σ ∈ B` with `u ∉ B ∩ EL_3(R)`.
  - *Why.*  For a compressor `u σ`, the element `1 + x^(σ n e_l) u E_ij u^-1` must be polynomial for every
    `n ≥ k`, and `n → ∞` detects the sign of each column of `σ`.  For a permutation `σ` it makes `Ad(u)` preserve
    `M_3(R_+)`, since the trace form has unit discriminant.  The scalars of the span of `B ∩ EL_3(R) - 1` form an
    `H_B`-invariant algebra containing all monomials of degree `≥ 2k`.  A line in the cone then puts `1` among
    them.
  - *What is left.*  The nonsofic side needs a `B ⊇ U_k` with `H_B` infinite and `B ∩ EL_3(R)` not generated
    by elementary matrices over a subring.  The span of that group already contains `M_3(F_q)`.  Or it needs a
    `B` containing no level `U_k`.  The natural next class is the elementary net groups `E(σ)`.  There the
    step to test is the passage from the span back to group elements.
- **w15-111, 2026-09-18: net subpairs and the span-to-group passage (class-killing obstruction).**
  - *Result.*  By [[net-sandwich-level-subpairs-cannot-certify-rank-three-cone]], take `B ⊇ U_k` with
    `-e_l ∈ cone(H_B · R_+^d)`.  Then the span of `B ∩ EL_3(R) - 1` contains `M_3(F_q)`.  Suppose also that
    `B ∩ EL_3(R)` lies between `e_ab(σ_ab)` and `1 + ⊕ σ_ab E_ab` for some pattern of entry spaces.  This
    holds for every elementary net group `E(σ)` and every group between `E(σ)` and `G(σ)`.  Then
    `e_ab(1) ∈ C` and `psi(C) = F`.  With (X1), (X2) and (W2), no such `B` is a Kun-Thom certificate.  A box
    level is not enough: `D (EL_3(F_q[x^(±1)][y_1, y_2]) x| SL_(d_1)(Z)) D^-1` with `D = diag(1, 1, y_1/y_2)`
    has a Kazhdan `B`, a net elementary part, and a line in the cone.  Its origin image lies in a Levi
    subgroup with nontrivial centraliser, but its edge maps onto a finite-index overgroup of `SL_2(F_q[x_1])`.
  - *Why.*  Conjugating level scalars `x^(2k e_i) I` through `H_B` and multiplying along a rational relation
    `-N e_l = Σ n_s h_s e_(i_s)` puts `x^(-2kN e_l) I` in the span.  The single-variable level element
    `x_l^(2kN) E_ab` then gives `E_ab`.  A pattern `1 + M(σ)` is a linear space, so the span cannot leave it,
    and `1 ∈ σ_ab` forces `e_ab(1)` into the group.
  - *What is left.*  With a level `U_k`, a certificate needs an elementary part that is not
    pattern-sandwiched.  Some `E_ab` lies in its span while `e_ab(1)` does not lie in the group, as for
    normal closures of `U_k` twisted by non-monomial `u`.  Without a level, the failure mode is a
    hypersurface level, and the edge must be Kazhdan in a new way.
- **w15-111, 2026-09-18: net subpairs and the span-to-group passage (class-killing obstruction).**
  - *Result.*  By [[net-sandwich-level-subpairs-cannot-certify-rank-three-cone]], take `B ⊇ U_k` with
    `-e_l ∈ cone(H_B · R_+^d)`.  Then the span of `B ∩ EL_3(R) - 1` contains `M_3(F_q)`.  Suppose also that
    `B ∩ EL_3(R)` lies between `e_ab(σ_ab)` and `1 + ⊕ σ_ab E_ab` for some pattern of entry spaces.  This
    holds for every elementary net group `E(σ)` and every group between `E(σ)` and `G(σ)`.  Then
    `e_ab(1) ∈ C` and `psi(C) = F`.  With (X1), (X2) and (W2), no such `B` is a Kun-Thom certificate.  A box
    level is not enough: `D (EL_3(F_q[x^(±1)][y_1, y_2]) x| SL_(d_1)(Z)) D^-1` with `D = diag(1, 1, y_1/y_2)`
    has a Kazhdan `B`, a net elementary part, and a line in the cone.  Its origin image lies in a Levi
    subgroup with nontrivial centraliser, but its edge maps onto a finite-index overgroup of `SL_2(F_q[x_1])`.
  - *Why.*  Conjugating level scalars `x^(2k e_i) I` through `H_B` and multiplying along a rational relation
    `-N e_l = Σ n_s h_s e_(i_s)` puts `x^(-2kN e_l) I` in the span.  The single-variable level element
    `x_l^(2kN) E_ab` then gives `E_ab`.  A pattern `1 + M(σ)` is a linear space, so the span cannot leave it,
    and `1 ∈ σ_ab` forces `e_ab(1)` into the group.
  - *What is left.*  With a level `U_k`, a certificate needs an elementary part that is not
    pattern-sandwiched.  Some `E_ab` lies in its span while `e_ab(1)` does not lie in the group, as for
    normal closures of `U_k` twisted by non-monomial `u`.  Without a level, the failure mode is a
    hypersurface level, and the edge must be Kazhdan in a new way.
- **w16-111, 2026-09-18: coefficient ring and the unit commutator (class-killing obstruction).**
  - *Result.*  By [[normalised-level-subpairs-cannot-certify-rank-three-cone]], take `B ⊇ U_k` with
    `-e_l ∈ cone(H_B · R_+^d)`.  The span of `B ∩ EL_3(R) - 1` is `M_3(A_B)`, where `A_B` is an
    `H_B`-invariant subring containing `x_l^(± 2kN)`.  So the pattern-sandwiched class of the net node is
    exactly the case `EL_3(A_B) ≤ E_B`.  Suppose `E_B` is normalised by `EL_3(A')` for a subring `A'`
    containing some `x^(-m)`, `m ∈ N^d \ {0}`.  Then `e_ab(1) = [e_ac(x^(nm)), e_cb(x^(-nm))] ∈ E_B`.  The
    same holds when `E_B ∩ EL_3(A')` has finite index in `EL_3(A')` and `A'` has a monomial unit.  In each
    case `C ⊇ SL_3(F_p)` and `C_F(psi(C)) = 1`.  This kills, with (X1), (X2) and (W2), every `E_B` normal in
    `GL_3(A_B)`, all conjugates `D EL_3(A) D^-1` (Picard-twisted ones included), all subnormal subgroups, and
    all finite-index subgroups containing `U_k` of every earlier level class.
  - *Why.*  The level element `e_ac(t)` with `t = x^(nm)` sits in `U_k`, and a normalising `e_cb(t^-1 s)`
    cancels the level from outside, which a span argument cannot do.  For a finite-index subgroup, a normal
    core has an ideal level `𝔞` of finite index, and the unit `t` satisfies `t^n ≡ 1 mod 𝔞`.
  - *What is left.*  With a level, a certificate needs a thin `E_B ⊆ SL_3(A_B)`.  It must span `M_3(A_B)`,
    must not be normalised by `EL_3(A_B)`, and must meet every `EL_3(A')` with a monomial unit in infinite
    index.  For instance `E_B ∩ SL_3(F_q[x_l^(± c)])` must contain `EL_3(x_l^c F_q[x_l^c])` but have infinite
    index.  The next tool is an intermediate-subgroup (arithmeticity) theorem for overgroups of a level.
- **w17-111, 2026-09-18: line sections of level subpairs (obstruction).**
  - *Result.*  By [[level-subpair-line-sections-are-bounded-or-cofinite]], take `B ⊇ U_k`, `m ∈ N^d \ {0}`,
    `t = x^m` and `n = ⌈k/|m|⌉`.  The line section `Δ_m = B ∩ SL_3(F_q[t^(±1)])` either has finite index in
    `SL_3(F_q[t^(±1)])` or fixes a lattice between `t^(2n) L_0` and `L_0`.  In the second case its elements
    have pole order at most `2n` at `t = 0`, and `Δ_m` is commensurable with `SL_3(F_q[t])`.  In the first
    case (Z3) of [[normalised-level-subpairs-cannot-certify-rank-three-cone]] gives `SL_3(F_p) ≤ C`.  So one
    element of `B` on a monomial line with a pole deeper than `2n` kills `B`.  The thin sections left open
    by w16-111 do not exist.
  - *Why.*  The closure of `Δ_m` in `SL_3(F_q((t)))` is open.  If it is unbounded it is everything, by
    Howe-Moore, and density gives `SL_3(F_q[t^(±1)]) = Δ_m · SL_3(F_q[t])`-type finite index.  If it is
    bounded it fixes a vertex, and the level `e_ab(t^n F_q[[t]])` pins that vertex near the base lattice.
  - *What is left.*  A level certificate needs `E_B` whose Laurent monomials enter only off the monomial
    lines.  The monomial-valuation groups `E_w = { g : v_w(g - 1) > 0 }` show such `E_B` exist.  The next
    tool is a monomial valuation preserved by the compressors of an infranormal `C`, which would contradict
    (W2).  Otherwise the positive side: sofic approximations of `T_3`.
- **w17-111, 2026-09-18: line sections of level subpairs (obstruction).**
  - *Result.*  By [[level-subpair-line-sections-are-bounded-or-cofinite]], take `B ⊇ U_k`, `m ∈ N^d \ {0}`,
    `t = x^m` and `n = ⌈k/|m|⌉`.  The line section `Δ_m = B ∩ SL_3(F_q[t^(±1)])` either has finite index in
    `SL_3(F_q[t^(±1)])` or fixes a lattice between `t^(2n) L_0` and `L_0`.  In the second case its elements
    have pole order at most `2n` at `t = 0`, and `Δ_m` is commensurable with `SL_3(F_q[t])`.  In the first
    case (Z3) of [[normalised-level-subpairs-cannot-certify-rank-three-cone]] gives `SL_3(F_p) ≤ C`.  So one
    element of `B` on a monomial line with a pole deeper than `2n` kills `B`.  The thin sections left open
    by w16-111 do not exist.
  - *Why.*  The closure of `Δ_m` in `SL_3(F_q((t)))` is open.  If it is unbounded it is everything, by
    Howe-Moore, and density gives `SL_3(F_q[t^(±1)]) = Δ_m · SL_3(F_q[t])`-type finite index.  If it is
    bounded it fixes a vertex, and the level `e_ab(t^n F_q[[t]])` pins that vertex near the base lattice.
  - *What is left.*  A level certificate needs `E_B` whose Laurent monomials enter only off the monomial
    lines.  The monomial-valuation groups `E_w = { g : v_w(g - 1) > 0 }` show such `E_B` exist.  The next
    tool is a monomial valuation preserved by the compressors of an infranormal `C`, which would contradict
    (W2).  Otherwise the positive side: sofic approximations of `T_3`.
- **w18-111, 2026-09-18: weight-bounded level subpairs (obstruction).**
  - *Result.*  By [[weight-bounded-level-subpairs-cannot-certify-rank-three]], for `B ⊇ U_k` let `W(E_B)`
    be the set of rational weights `w` such that `E_B` fixes a point of the Bruhat-Tits building of
    `SL_3` over the `v_w`-completion.  Then `W(E_B)` is `H_B`-invariant and lies in the dual cone of
    `cone(H_B · R_+^d)`.  With (X1) and (W2) this puts every weight of a surviving `B` to zero on the
    invariant core `M ≠ ∅`.  So no `B` whose `E_B` fixes a point for one strictly positive weight is a
    certificate.  This kills the E_w-type groups left by w17-111, every parahoric and every conjugate.
  - *Why.*  The level forces bounded weights into the positive orthant: `e_12(x_l^n) e_21(x_l^n)` has
    trace of negative valuation when `w_l < 0`.  Each `u σ ∈ B` carries a fixed point in `X_w` to one in
    `X_(σ^T w)`.  No compressor-invariant valuation is needed, since all of `B` permutes the buildings.
  - *What is left.*  A certificate needs `E_B` with no fixed point in any positive-weight building meeting
    `M`, while `C` fixes the base vertex of each and every monomial line section is bounded.  Next: show
    that unboundedness in `X_(1,..,1)` concentrates on one monomial line after conjugating by `Gamma`,
    which would reach (L2).  Otherwise, the positive side.
- **w19-111, 2026-09-19: line concentration refuted (method obstruction).**
  - *Result.*  By [[level-groups-need-not-concentrate-on-monomial-lines]], for a level group `E ⊇ U_k`,
    `E` fixes a point of the weight-`w` building iff `w` pairs nonnegatively with every exponent in the
    supports of the traces of `E` (Bass's lemma).  So `W(E_B)` is the rational dual of the trace Newton cone.
    Unboundedness always concentrates on monomial curves `x^m ↦ t^(<a, m>)`, where (L1) makes the image
    cofinite.  But it need not concentrate on any monomial line: for `θ > 0` with independent coordinates,
    `E_θ = E_3(F_q[P_θ], I_θ)`, `P_θ = { <θ, p> > 0 } ∪ 0`, contains `U_1`, avoids `e_ab(1)`, is normalised
    by `Gamma`, fixes no point of any `X_w`, and has pole-free sections on every monomial line.
  - *Why.*  The Newton cone of `E_θ` is an irrational half-space, which no rational weight sees and which meets
    no monomial line in a negative ray.  Only the normaliser kills `E_θ`: it preserves the half-space, so
    `H_B` fixes the ray of `θ` and is abelian.
  - *What is left.*  The step proposed by w18-111 is false, and no statement about `E_B` alone closes the
    level class.  A closing argument must move a deep trace monomial along the orbit of a nonnegative
    `σ ∈ H_B` of infinite order onto a monomial line.  Otherwise, the positive side.
- **w20-111, 2026-09-19: Perron-Frobenius compressors (method obstruction and reduction).**
  - *Result.*  By [[perron-frobenius-compressors-cannot-close-the-level-class]], the σ-step proposed by
    w19-111 is false.  For a primitive nonnegative `σ ∈ SL_d(Z)` with `σ^T θ = λ θ`, `θ > 0`, the split
    subpair `B_σ = E_θ x| <σ>` has `U_1 ≤ E_B`, `psi(C) = 1`, `C` infranormal and not normal, and `σ` a
    compressor.  Its traces have monomials with `<w, p> < 0` for every rational `w`.  Yet all traces and
    their `σ`-orbits stay in `{ <θ, ·> > 0 }`, and every monomial line section is pole-free.  It fails only
    (T).  For a survivor, one primitive compressor forces `Ncone(E_B) = R^d` and `W(E_B) = ∅`, the Newton
    data of `EL_3(R)`.  Compressor twists `u` obey
    `v_w(u e_a) + v_w(e_b^T u^-1) ≥ -k min_i (σ^T w)_i`.
  - *Why.*  `σ` preserves the half-space of its Perron functional, and negative monomial rays lie outside
    it.  For a survivor, Perron-Frobenius pushes every weight of `D(E_B)` to `θ_σ > 0`, which the invariant
    core forbids.
  - *What is left.*  Neither a single compressor nor any Newton or weight invariant closes the level class.
    If a generating set of nonnegative compressors is untwisted, (W2) and (M2) kill `B`.  So a survivor needs
    essential, bounded twists over a character-free `H_B`.  The next step is to show that such twists are
    coboundaries modulo `E_B`, starting with diagonal twists and `H^1(H_B, Q^d) = 0`.  Otherwise, the positive
    side.
- **w21-111, 2026-09-19: monomial twists cancel around loops (class-killing obstruction).**
  - *Result.*  [[monomial-twisted-level-subpairs-cannot-certify-rank-three]] kills every `B ⊇ U_k`
    whose projection `H_B`, after conjugating `B` by some `γ ∈ Gamma`, is virtually lifted by monomially
    twisted elements.  This covers diagonal twists `diag(x^δ(σ))` for arbitrary `δ`, signed-permutation
    twists, twists in any finite `σ̂`-invariant group, and the untwisted case (Q4), all up to finite index.
    No cohomology (`H^1(H_B, Q^d) = 0`), boundedness or coboundary step is needed.
  - *Why.*  For a monomial `c = D π σ`, the double commutator
    `[[e_xy(β), c e_ab(x^m) c^-1], c e_ba(x^m') c^-1] = e_xy(β x^(σ(m+m')))`: the twist `d_y / d_z` of the edge
    `y → z` cancels around the loop.  A line in `K0(H_mon)` walks `e_xy(α x^(2k e_i))` down to `e_xy(α)`.
    Finite index keeps the cone for nonnegatively generated groups (T2), and `Gamma`-conjugates keep the level
    `U_(2k)` (T4).
  - *What is left.*  A level certificate now needs essential non-monomial twists: for every `γ`, only an
    infinite-index subgroup of `H_B` lifts monomially.  The loop calculus for lower-triangular (Borel) twists
    reaches only the lowest root, giving `X_31(F_q) ≤ C` (T5).  The next step is to decide whether a Kazhdan
    `B = < U_k, u_i σ_i >` with lower unitriangular Laurent `u_i` can have `psi(C) ≤ C_F(X_31)`.  Either
    build it, as the first twisted candidate, or run the loop calculus for parabolic twists.
