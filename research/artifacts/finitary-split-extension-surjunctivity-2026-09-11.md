# Finitary split extensions of surjunctive groups are surjunctive; group doubles

Lane `gottschalk-positive`, 2026-09-11. This extends
`research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md` (below called
[W]) from permutational wreath products to an abstract finitary setting. The
new instance is the group double `G *_Gamma G`.

## Theorem 0 (finitary split extensions)

Let `W = N semidirect_alpha G` with product
`(f,g)(f',g') = (f alpha_g(f'), gg')`, and let `X` be a left `G`-set. A
*finitary structure* on `W` consists of the following.

* **(D)** For each finite `S` in `X`, an epimorphism `p_S: N -> N_S` onto a
  residually finite group, with `N_empty = 1`.
* **(D')** For `U` contained in `S`, injective homomorphisms
  `iota_(U,S): N_U -> N_S` with `iota_(V,S) = iota_(U,S) iota_(V,U)`.

The data must satisfy:

* **(A1) Detection.** For finitely many nontrivial `n_1,...,n_k in N` there
  is `S` with every `p_S(n_i) != 1`.
* **(A2) Finite support.** Each `n in N` has a finite `L(n)` in `X` such that
  for all `g in G` and `U` contained in `S`: if `g L(n)` misses `S\U`, then
  `p_S(alpha_g n) = iota_(U,S)(p_U(alpha_g n))`.
* **(A3) Stabilizer invariance.** `p_S o alpha_k = p_S` for every `k` in the
  pointwise stabilizer `G_S`.

**Theorem 0.** If `W` carries a finitary structure, then `W` is surjunctive
if and only if `G` is surjunctive.

## Instances

**(I1) Permutational wreath products.** `N = direct_sum_X A` with `A`
residually finite, `alpha_g(n)(x) = n(g^-1 x)`.
* `N_S = A^S`, and `p_S` is restriction to `S`.
* `iota` extends by `1`.
* `L(n) = supp(n)`.

(A1)-(A3) are immediate. This recovers Theorem 1 of [W].

**(I2) Group doubles.** Let `Gamma <= G`, `X = G/Gamma`, `x_0 = Gamma`, and
`D = G *_Gamma Ghat`.

**Lemma 5.1.** Let `F` be the free group on `{e_x : x in X \ {x_0}}`, put
`e_(x_0) = 1`, and define

```text
alpha_g(e_x) = e_(gx) e_(g x_0)^-1.
```

Then `alpha` is an action of `G` by automorphisms and `D ~= F semidirect_alpha G`.

*Proof.*
* *Action.* `alpha_(g') alpha_g (e_x) = e_(g'gx) e_(g'x_0)^-1 e_(g'x_0) e_(g'gx_0)^-1 = alpha_(g'g)(e_x)`,
  and `alpha_g(e_(x_0)) = 1` is consistent.
* *Map `Phi: D -> F semidirect G`.* Send `g` to `(1,g)` and `ghat` to
  `(e_(g x_0)^-1, g)`.
  * On `Ghat`: `(e_(gx_0)^-1, g)(e_(hx_0)^-1, h) = (e_(gx_0)^-1 alpha_g(e_(hx_0))^-1, gh) = (e_(ghx_0)^-1, gh)`,
    so `Phi` is a homomorphism there.
  * For `gamma in Gamma`, `gammahat -> (e_(x_0)^-1, gamma) = (1, gamma)`, so
    the two copies agree on `Gamma` and `Phi` is well defined.
* *Inverse `Psi`.* Send `(1,g)` to `g` and `(e_(g x_0), 1)` to `g ghat^-1`.
  * Well defined: `g gamma (g gamma)hat^-1 = g ghat^-1`.
  * The only relations of the semidirect product are those of `G`, those of
    the free group (none), and the conjugation rule
    `g' Psi(e_(gx_0)) g'^-1 = Psi(e_(g'gx_0)) Psi(e_(g'x_0))^-1`. The
    right side is
    `(g'g)(g'g)hat^-1 (g' g'hat^-1)^-1 = g'g ghat^-1 g'hat^-1 g'hat g'^-1 = g' (g ghat^-1) g'^-1`,
    which is the left side. So `Psi` is a homomorphism.
* *Mutual inverses.* `Psi Phi(ghat) = (g ghat^-1)^-1 g = ghat`, and
  `Phi Psi(e_(gx_0),1) = (1,g)(alpha_(g^-1)(e_(gx_0)), g^-1) = (e_(gx_0),1)`.
  QED

Finitary structure on `D`:
* `N_S = F_S`, the free group on `S \ {x_0}`, which is residually finite.
* `p_S` kills basis elements outside `S`, and `iota` is inclusion of free
  factors.
* `L(w)` is the set of letters of `w`, together with `x_0`.

Checking the axioms:
* **(A1).** A nontrivial word survives `p_S` once `S` contains its letters.
* **(A2).** The letters of `alpha_g(w)` lie in `g L(w)`, and deleting letters
  outside `S` that avoid `S\U` is the same as deleting them from `F_U`.
* **(A3).** Let `k in G_S`. Then `k` fixes `S` pointwise and preserves
  `X\S`. So `p_S(e_(ky)) = p_S(e_y)` for every `y`, while
  `p_S(e_(kx_0)) = 1`: either `x_0` is not in `S` and `k x_0` is not in `S`,
  or `x_0` is in `S` and `e_(kx_0) = e_(x_0) = 1`. Since
  `alpha_k(e_y) = e_(ky) e_(kx_0)^-1`, this gives `p_S alpha_k = p_S`.

**Corollary 6.** For every group `G` and every subgroup `Gamma`, the double
`G *_Gamma G` is surjunctive if and only if `G` is.

**Corollary 7.** Let `(Gamma, G)` be the Kun--Thom Theorem E pair. Then the
group double `G *_Gamma G` is surjunctive and not sofic: nonsofic by Theorem A,
version 3, arXiv:2608.06222; surjunctive by Corollary 6 and residual
finiteness of `G`. It is finitely generated. This is a second witness for
`surjunctive-nonsofic-group-exists`.

## Proof of Theorem 0

The only-if direction is subgroup heredity ((F2) of [W]). Assume `G` is
surjunctive and `tau = (M, mu)` is an injective cellular automaton over `W`,
with `m = (f_m, g_m)`.

**Coset spaces.**
1. Given finite `S` and a finite quotient `q: N_S -> Q`, put
   `H_(S,q) = ker(q o p_S)`. This is a normal subgroup of `N`, hence a
   subgroup of `W`.
2. Because `(h,1)(f,g) = (hf, g)`, the coset space is
   `Omega = H_(S,q)\W ~= Q x G`.
3. For `U` contained in `S` put `Q_U = q(iota_(U,S)(N_U))` and
   `H_(U) = ker(q o iota_(U,S) o p_U)`, so that `H_(U)\W ~= Q_U x G`.
4. The transplants are

```text
tau_U(y)(u,g) = mu( ( y(u . c^U_m(g), g g_m) )_(m in M) ),
c^U_m(g) = q(iota_(U,S)(p_U(alpha_g f_m))) in Q_U.                  (T)
```

**Separation.** For distinct `w, w'` in a finite set with the same
`G`-coordinate, `w' w^-1 = (f,1)` with `f != 1`. By (A1) some `S` detects all
of these, and residual finiteness of `N_S` gives one finite quotient `q`
detecting their images. This is the analogue of Lemma 2.1 of [W]; Lemma 1.2
of [W] then reduces surjectivity of `tau` to surjectivity of every `tau_S`.
By Lemma 1.1 of [W], every `tau_U` is injective.

**Strata.** Let `L = union_m L(f_m)`, `Z_s = {g : s in gL}` and
`G_s = Stab_G(s)`.
* `Z_s` is a finite union of right cosets of `G_s` (Lemma 2.2 of [W]).
* By (A2), if `g` lies in no `Z_s` with `s in S\U`, then
  `c^S_m(g) = c^U_m(g)`, which lies in `Q_U`.
* By (A3), `c^U_m(kg) = c^U_m(g)` for `k in G_U`, so `tau_U` commutes with
  left translation by `G_U` on the `G`-coordinate.
* Every map built from `tau_U` also commutes with left multiplication by
  `Q_U` on the fiber coordinate, since (T) multiplies on the right.

**Slices.** For `V` contained in `U`, the fibers of `B^(Q_U x G)` over the
left cosets `cQ_V` are identified with `B^(Q_V x G)` by `v -> q_c v`. The
choice of `q_c` does not matter, because the relevant maps commute with left
`Q_V`-translation. The slicewise extension `phi^[U]` acts as `phi` on each
fiber. Away from the strata of `U\V`, `tau_U = tau_V^[U]` on each fiber
(analogue of Lemma 2.3 of [W]).

**Peeling.** With `A^U` replaced by `Q_U` and products replaced by left
cosets, Proposition 4.1 of [W] and its proof hold verbatim.
* Its steps (1)-(3) use only the strata, slice compatibility, and the
  pointwise-identity property of inverses off `Q_(U')`.
* The final step applies Lemma 3.1 of [W] with `K = G_U`, which is
  surjunctive as a subgroup of `G`.

This gives bijectivity of `rho_S` and hence surjectivity of `tau_S`. QED

## Remarks

* **The coset wreath `W_3`.** `arithmetic-coset-wreath-is-not-sofic` concerns
  `W_3 = (direct_sum_(Gamma/Lambda) C_2) semidirect SL_3(Z[1/3])`. Instance
  (I1) and residual finiteness of `SL_3(Z[1/3])` make `W_3` surjunctive,
  whatever its soficity.
* **Amalgams in general.** For `A *_C B` with `A != B` there is no fold map,
  and the method does not apply as stated.
* **What this does not settle.** It does not decide surjunctivity of:
  * the binary Leavitt unit group;
  * Thompson's `V`;
  * the Fournier--Facio torsion-free group;
  * any group without a finitary split structure over a surjunctive quotient.
