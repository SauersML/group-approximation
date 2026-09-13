# UN (U3): the stable-finiteness boundary for elementary groups over simple rings

Lane `un-converse`, 2026-09-13. Status: Lemmas 1–2, Theorem A, Corollary B, Theorem C and Example D are
proved below. **None of it has been reviewed.** Credits:
- Theorem [full complementary idempotents] of `non_mf_groups_exist.tex` (l.918) and Cor l.1016 do all the
  Kazhdan work; Theorem A only moves them along matrix amplifications. `un-prior-art` independently noted
  the identity `E_k(M_m(R)) = E_(km)(R)` and its consequence for simple rings.
- Malcev (residual finiteness of finitely generated linear groups), Elek–Szabó (LEF ⇒ sofic).
- The step-3.3 argument of `research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`
  is the finite-field case of Theorem C.
- Reduction of the Weyl algebra mod p (Example D) is classical folklore.

Conventions: rings are unital and associative; `e_ij(r) = 1 + r E_ij`; `E_N(R) = EL_N(R)`; the commutator is
`[g,h] = g h g^-1 h^-1`; `X_ij = {e_ij(r) : r ∈ R}` is a root subgroup. An algebraic ultraproduct is
`∏_ω M_(d_k)(F_k)` with commutative fields `F_k` and a nonprincipal ultrafilter `ω`. A ring is **exactly
matricial** if it embeds as a unital ring in such an ultraproduct.

## 0. The picture for a countable simple unital ring R ≠ 0

```text
exactly matricial  ==>  GL_N(R), E_N(R) LEF for all N  ==>  E_N(R) MF (and sofic) for all N     (Thm C)
      |                                                              |
      v                                                              v
stably finite  <==  E_N(R) has a nontrivial MF quotient for infinitely many N                     (Cor B)
      |
      v
directly finite  <==  E_N(R) has a nontrivial MF quotient for one N >= 2                           (Cor l.1016)
```

More precisely (Cor B(ii)): a nontrivial MF quotient of `E_N(R)` forces `M_m(R)` to be directly finite for
every `m <= N/2`. So *stable* MF approximability of the Kazhdan groups `E_N(R)` sits between exact
matricial embeddability and stable finiteness. The two open converses are in §5.

## 1. Two lemmas on elementary groups

**Lemma 1 (block identification).** Let `m >= 1` and `n >= 2`. Identify `M_n(M_m(R)) = M_(nm)(R)` by blocks,
with coordinate `(i,a)` for block `i` and position `a`. Then `E_n(M_m(R)) = E_(nm)(R)`.

*Proof.* (⊆) For block indices `i ≠ j` and `A ∈ M_m(R)`,
`e_ij(A) = ∏_(a,b) e_((i,a),(j,b))(A_ab)`. The factors commute and their off-diagonal parts multiply to zero,
since `E_((i,a),(j,b)) E_((i,a'),(j,b')) = 0` when `i ≠ j`.
(⊇) A generator `e_((i,a),(j,b))(r)` with `i ≠ j` is the block generator `e_ij(r E_ab)`. If `i = j` and
`a ≠ b`, choose a block `k ≠ i` (possible because `n >= 2`). For distinct coordinates `p, q, s` the Steinberg
relation `[e_pq(x), e_qs(y)] = e_ps(xy)` holds: expanding,
`(1+xE_pq)(1+yE_qs)(1−xE_pq)(1−yE_qs) = 1 + xy E_ps`. Therefore

```text
e_((i,a),(i,b))(r) = [ e_((i,a),(k,1))(r) , e_((k,1),(i,b))(1) ],
```

a commutator of two cross-block generators. ∎

**Lemma 2 (root subgroups are conjugate).** Let `N >= 2` and `i ≠ j`. Some `w ∈ E_N(R)` satisfies
`w X_ij w^-1 = X_12`.

*Proof.* For `p ≠ q` put `w_pq = e_pq(1) e_qp(−1) e_pq(1) ∈ E_N(R)`. On the plane of coordinates `p, q` it is
`[[0,1],[−1,0]]`, and it fixes the other basis vectors. So `w_pq ε_k = ±ε_(τk)` with `τ = (p q)` and central
signs. Since `w_pq` has entries in `{0, ±1}`, `w_pq E_kl w_pq^-1 = ±E_(τk,τl)`, and hence
`w_pq e_kl(r) w_pq^-1 = e_(τk,τl)(±r)`. Because `r ↦ −r` is a bijection of `R`,
`w_pq X_kl w_pq^-1 = X_(τk,τl)`. Transpositions generate `S_N`, and `S_N` is transitive on ordered pairs of
distinct indices. ∎

## 2. Theorem A: the full-defect criterion along matrix amplifications

**Theorem A.** Let `R` be a countable unital ring and `m >= 1`. Suppose `s, t ∈ M_m(R)` satisfy

```text
ts = 1,        M_m(R) (1 − st) M_m(R) = M_m(R).
```

Then for every `N >= 2m`, every homomorphism from `E_N(R)` to an MF group is trivial.

*Proof.* `M_m(R)` is a countable unital ring satisfying the hypothesis of the printed Theorem [full
complementary idempotents] (l.918, verbatim: "For every n ≥ 2, every homomorphism from EL_n(R) to an MF group
is trivial"). With `n = 2`, every homomorphism from `E_2(M_m(R))` to an MF group is trivial. By Lemma 1,
`E_2(M_m(R)) = E_(2m)(R)`.

Let `N >= 2m` and `φ : E_N(R) → M` with `M` an MF group. The copy of `E_(2m)(R)` on the first `2m`
coordinates is a subgroup of `E_N(R)`, so `φ` is trivial on it, and in particular `φ(X_12) = 1`. By Lemma 2
every root subgroup is conjugate to `X_12`, so `φ(X_ij) = 1` for all `i ≠ j`. The root subgroups generate
`E_N(R)`, so `φ = 1`. ∎

*Variant using only the Cairn rank-four node.* `full-complementary-idempotent-elementary-full-mf-radical`
states the criterion for `n >= 4`. Using it in place of l.918 gives the same conclusion for `N >= 4m`.

## 3. Corollary B: simple rings

**Corollary B.** Let `R` be a countable simple unital ring.
1. If `M_m(R)` is not directly finite, then for every `N >= 2m`, every homomorphism from `E_N(R)` to an MF
   group is trivial.
2. If `R ≠ 0` and `E_N(R)` has a nontrivial homomorphism to an MF group (for instance, if `E_N(R)` is MF),
   then `M_m(R)` is directly finite for every `m <= N/2`.
3. If `E_N(R)` has a nontrivial MF quotient for infinitely many `N`, then `R` is stably finite. Since MF passes
   to subgroups, this holds in particular when `E_N(R)` is MF for all `N`.

*Proof.* (1) `M_m(R)` is simple, because its two-sided ideals are the `M_m(I)`. Take `x, y ∈ M_m(R)` with
`xy = 1 ≠ yx` and set `t = x`, `s = y`. Then `ts = 1 ≠ st`, and `e = 1 − st` is a nonzero idempotent
(`e^2 = 1 − 2st + s(ts)t = e`). Its two-sided ideal is nonzero, hence all of `M_m(R)`, and Theorem A applies.
(2) This is the contrapositive of (1). If `E_N(R)` is MF and `R ≠ 0`, the identity map is a nontrivial
homomorphism to an MF group, since `e_12(1) ≠ 1`.
(3) By (2), every `M_m(R)` is directly finite. ∎

**Model tests.**
- `R = L_k(1,2)` is simple and `R` itself is not directly finite (`m = 1`). So `E_N(R)` has no nontrivial MF
  quotient for every `N >= 2`, which recovers Cor l.1016.
- `R = LC(X, F_q) ⋊ Z` (the Pestov ring) is simple and exactly matricial, so the conclusion of B is vacuous
  and Theorem C gives the LEF side.
- `R = M_d(F)` is simple and matricial, and `E_N(R) = E_(Nd)(F) = SL_(Nd)(F)` is linear, hence LEF and MF. B is
  vacuous, as it should be.

## 4. Theorem C: exact matricial embeddability gives LEF over arbitrary fields

**Theorem C.** Let `R` be a countable unital ring with an injective unital ring homomorphism
`Ψ : R → ∏_ω M_(d_k)(F_k)`, where the `F_k` are arbitrary commutative fields. Then for every `N >= 1`,
`GL_N(R)` is LEF. So every subgroup of it, including `E_N(R)`, is LEF, and hence sofic, hyperlinear and MF.

*Proof.*
1. *Matrices and units.* `M_N(∏_ω A_k) = ∏_ω M_N(A_k)` as rings, so `Ψ` induces an injective unital ring
   homomorphism `M_N(R) → ∏_ω M_(N d_k)(F_k)`. An element of the ultraproduct is invertible iff ω-almost all
   of its coordinates are invertible, with the inverse taken coordinatewise. This gives an injective group
   homomorphism `GL_N(R) → ∏_ω GL_(N d_k)(F_k)`.
2. *A finite window.* Let `F ⊆ GL_N(R)` be finite. The finitely many equalities `fg = h` and inequalities
   `f ≠ g` (for `f, g, h ∈ F`) hold in ω-almost every coordinate. Fix one such coordinate `k` and let
   `ψ : F → GL_(N d_k)(F_k)` be the coordinate map. It is injective on `F` and satisfies `ψ(fg) = ψ(f)ψ(g)`
   whenever `f, g, fg ∈ F`.
3. *Malcev.* `Λ = ⟨ψ(F)⟩` is a finitely generated subgroup of `GL_(N d_k)(F_k)`, so it is residually finite
   (Malcev, 1940). Choose a finite-index normal subgroup `Δ` of `Λ` containing none of the finitely many
   elements `ψ(f)ψ(g)^-1` with `f ≠ g ∈ F`. Then `F → Λ/Δ` is injective and partially multiplicative, so
   `GL_N(R)` is LEF.
4. *Consequences.* LEF ⇒ sofic (Elek–Szabó), and sofic ⇒ hyperlinear. LEF ⇒ MF: enumerate
   `G = {g_1, g_2, …}` and take partial embeddings `ψ_n : {g_1, …, g_n} → Q_n` into finite groups. Put
   `V_n(g) = λ_(Q_n)(ψ_n(g))`, the left-regular permutation unitary, on the window (and `1` off it). These
   maps are exactly multiplicative on growing windows, and for `g ≠ 1`,
   `‖V_n(g) − 1‖ >= ‖(λ(ψ_n(g)) − 1) δ_e‖ = √2`. So `g ↦ [(V_n(g))]` is an injective corona homomorphism, and
   `G` is MF (Lemma l.351). ∎

*Remark.* Step 3 is where the fields matter. For finite `F_k` the coordinate groups are already finite, which
is the Pestov argument; Malcev lets `F_k` be any fields, including characteristic 0.

## 5. Example D: a simple domain with no finite-dimensional representations that is exactly matricial

Let `A_1(Q) = Q<x,y>/(yx − xy − 1)`, the Weyl algebra. It is simple, and in characteristic 0 it has no nonzero
finite-dimensional module (trace of `yx − xy` would be 0). It is nevertheless exactly matricial:
- For a prime `p`, let `T_p` be multiplication by `t` and `D_p = d/dt` on `F_p[t]/(t^p)`. For `j < p−1`,
  `[D_p, T_p] t^j = (j+1)t^j − j t^j = t^j`, and `[D_p, T_p] t^(p−1) = 0 − (p−1) t^(p−1) = t^(p−1)`. So
  `D_p T_p − T_p D_p = 1` in `M_p(F_p)`.
- Take `ω` on the primes. `Q → ∏_ω F_p`, `a/b ↦ (a b^-1 mod p)`, is a unital ring homomorphism, and
  `x ↦ (T_p)`, `y ↦ (D_p)` extends it to a unital ring homomorphism `A_1(Q) → ∏_ω M_p(F_p)` (coordinatewise on
  PBW normal forms, for `p` beyond the denominators).
- Its kernel is a proper two-sided ideal of a simple ring, hence 0.

By Theorem C, every `GL_N(A_1(Q))` is LEF. So "no finite-dimensional representations" is not an obstruction on
the LEF side; the obstruction that matters is infiniteness. `A_1(Q)` is not finitely generated, so its
elementary groups are not Kazhdan.

## 6. What stays open, and firewalls

- **(O1) Is stable finiteness enough?** For a countable simple stably finite ring `R`, is `E_N(R)` MF, or does
  it at least have a nontrivial MF quotient, for all `N`? (Cairn: `stably-finite-simple-rings-have-mf-elementary-groups`.)
  - *Ring-level firewall (un-prior-art).* Greenfeld arXiv:2210.11650 gives finitely generated stably finite
    non-linear-sofic algebras, but they are not simple. Stable finiteness alone does not make a ring matricial.
    A counterexample to O1 must therefore either be simple and non-matricial, or produce MF approximations of
    `E_N(R)` that are not induced by ring models.
  - *Possible source of a negative answer.* The MF problem for C*-algebras fails (MIP* = RE ⇒ a stably finite
    non-MF C*-algebra). Transferring that failure to a simple ring `R` and to the non-unitary groups `E_N(R)` has
    no known mechanism.
- **(O2) Converse of Theorem C.** If `E_N(R)` is MF, or LEF, for all `N`, is `R` exactly matricial, or does it
  at least have a Sylvester rank function? (Cairn: `stably-mf-elementary-groups-force-matricial-rings`.)
  - *Firewall.* Operator-norm models of `E_N(R)` send root subgroups to unitaries. Nothing forces a ring
    homomorphism out of them, and the rank-model analogue (`el3-rank-models-factor-through-ring-rank-models`)
    is itself open.
- **(O3) The rank window below 2m.** If `M_m(R)` is infinite but `M_(m−1)(R)` is finite, Theorem A says nothing
  about `E_N(R)` for `N < 2m`. The printed compression cell needs a spare coordinate block over the infinite
  ring, and I found no cell of size `m+1`.
- **(O4) The MF/sofic split (hand-off to un-middle).** Operator-norm models die from infiniteness (Theorem A).
  Over finite fields, Hamming models are known to die from a *halvable* idempotent `eA ≅ eA ⊕ eA`
  (`halvable-corner-makes-elementary-groups-nonsofic`). A simple ring that is not stably finite but has no
  halvable idempotent in any `M_d(R)` would give elementary groups with no MF quotient in large rank whose
  soficity is untouched by any known obstruction. That would make them candidates for simple (and, over a
  finitely generated ring, Kazhdan) sofic non-MF groups. Whether such simple rings exist is open here.
