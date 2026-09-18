---
rg: 2
id: fpbs-fibered-mod-p-certificates-refute-luck-approximation-proof
kind: route
title: The Fox block tI - J bounds mod-p homology of every cover and is invertible over twisted Laurent series
target: fpbs-fibered-mod-p-certificates-refute-luck-approximation
requires:
  - fpbs-fg-by-cyclic-farber-chains-bounded-type-reduction
artifacts:
  - experiments/mapping-torus-inner-quotients-2026-09-17/foxnull.g
  - experiments/mapping-torus-inner-quotients-2026-09-17/foxnull.out
---

# Proofs

Notation. `N` is either the free group `F_d = <x_1..x_d>` or a closed surface
group `pi_1(S_g) = <x_1..x_{2g} | R>` (then `d = 2g`). `phi` is in `Aut(N)` and
`Gamma = N x|_phi Z = <x_1..x_d, t | (R), r_i = t x_i t^-1 phi(x_i)^-1>`.
`p` is a prime, `k = F_p`. For a Farber chain `(Gamma_n)` put `G_n = Gamma/Gamma_n`
and `d_p(H) = dim_k H_1(H;k)`. Fox derivatives are left derivatives, so
`d(uv)/dx = du/dx + u dv/dx`. Matrices over a ring act on row vectors from the
right. For `A` in `M_{m x l}(k[Gamma])` write `A_n` for its image over `k[G_n]`
and `null(A_n) = dim_k { v in k[G_n]^m : v A_n = 0 }`.

Put `J = (d phi(x_i)/d x_j)_{i,j<=d}` in `M_d(k[N])` and `B = tI - J` in `M_d(k[Gamma])`.

## 1. Homology of covers is bounded by the Fox block

**Lemma 1.1.** `d r_i / d x_j = t delta_ij - d phi(x_i)/d x_j` in `k[Gamma]`, and
`d r_i / d t = 1 - t x_i t^-1 = 1 - phi(x_i)`. So the `x`-block of the Fox matrix
of the relators `r_i` is exactly `B`.

*Proof.* `d(t x_i t^-1 phi(x_i)^-1)/dx_j = t delta_ij + t x_i t^-1 d(phi(x_i)^-1)/dx_j`,
and `d(w^-1)/dx = -w^-1 dw/dx`. In `Gamma`, `t x_i t^-1 phi(x_i)^-1 = 1`. The
`t`-derivative is `1 + t x_i d(t^-1)/dt = 1 - t x_i t^-1`. []

**Proposition 1.2.** For every finite quotient `G_n` of `Gamma` (any type, not only inner)
and every prime `p`:

    d_p(Gamma_n) - 1 <= null(B_n).

For `N = F_d` the left side equals `null(F_n)`, where `F` is the full `d x (d+1)` Fox matrix.

*Proof.* The presentation 2-complex `Y` has `pi_1 Y = Gamma`. Its cover `Y_n` with
group `G_n` has `pi_1 Y_n = Gamma_n`, and its cellular chain complex over `k` is
`k[G_n]^{c_2} --dF_n--> k[G_n]^{c_1} --> k[G_n]`. The second map is
`v -> (v(x_j - 1), v(t-1))`, with image of dimension `|G_n| - 1` since `Y_n` is connected.

Free case. `c_2 = d` and `c_1 = d+1`. So
`d_p(Gamma_n) = ((d+1)|G_n| - (|G_n| - 1)) - (d|G_n| - null(F_n)) = 1 + null(F_n)`.
Since `F = [B | c]`, every `v` with `vF_n = 0` has `vB_n = 0`. So `null(F_n) <= null(B_n)`.

Surface case. `c_2 = d+1` (rows `R, r_1..r_d`) and `c_1 = d+1`. We have `dR/dt = 0`,
so `F = [[dR/dx, 0], [B, c]]`. The same count gives
`d_p(Gamma_n) = 1 - |G_n| + null(F_n)`. A kernel vector is `(v_0, w)` with
`v_0` in `k[G_n]` and `v_0 (dR/dx)_n + w B_n = 0`. For fixed `v_0` the admissible `w`
form a coset of `ker(. B_n)` or are empty. So `null(F_n) <= |G_n| + null(B_n)`. []

**Proposition 1.3 (inner type: the certificate is a fixed space of the lifted monodromy).**
Let `(Gamma_n)` be of inner type, `N_n = N cap Gamma_n`. Then `[N:N_n] = |G_n|`, and there is
`s = t n_0` in `Gamma_n` (`n_0` in `N`) with `Gamma_n = N_n x|_psi <s>`, `psi = conjugation by s`.
With `psi_*` acting on `V_n = H_1(N_n;k)`:

    d_p(Gamma_n) = 1 + dim ker(psi_* - I on V_n),   dim V_n = (d-1)|G_n| + 1 (free),  (d-2)|G_n| + 2 (surface).

*Proof.* `N -> G_n` is onto, so `[N:N_n] = |G_n|`, and some `n_0` in `N` has `t n_0` in `Gamma_n`.
`Gamma_n/N_n` embeds in `Gamma/N = Z` and contains the image of `s`, so `Gamma_n = N_n x| <s>`.
For a semidirect product with `Z`, `H_1(Gamma_n;k) = H_1(N_n;k)_psi (+) k`, and
`dim coker(psi_* - I) = dim ker(psi_* - I)` on the finite-dimensional `V_n`. The dimension
of `V_n` is the Schreier formula, respectively the Euler characteristic of the degree-`|G_n|` cover. []

So a linear lower bound on `d_p` along an inner-type chain says exactly that the lifted
monodromies have an eigenvalue-1 space occupying a positive proportion of `H_1` of the
fiber covers mod `p`. Theorem 3.1 below says Lück approximation for `tI - J` forbids this.

## 2. The block has full rank over the natural division ring

**Lemma 2.1.** Let `D_N` be a division ring containing `k[N]` to which `phi` extends as
an automorphism. Then `k[Gamma]` embeds in the twisted Laurent series division ring
`E = D_N((t^-1; phi))`, whose elements are `sum_{i <= i_0} a_i t^i` with
`t a = phi(a) t`. `B` is invertible in `M_d(E)`.

*Proof.* `E` is a division ring. This is standard for skew Laurent series over a
division ring with an automorphism: invert the leading term. The map `x -> x`,
`t -> t` respects the defining relation, and it is injective because
`k[Gamma] = oplus_i k[N] t^i`. Write `B = t(I - t^-1 J)`. The matrix
`Q = t^-1 J` has entries of `t`-degree `-1`, so `sum_{m>=0} Q^m` converges
coefficientwise in `M_d(E)`: the degree `-m` part only receives terms with at
most `m` factors. It inverts `I - Q`. So `B^-1 = (I-Q)^-1 t^-1`. []

For `N = F_d`, take `D_N` to be Cohn's universal field of fractions of the free
algebra `k[F_d]` (a fir). Automorphisms extend by universality. For the surface
case, take the Hughes-free division ring `D_{k[N]}` (surface groups are bi-orderable,
so the Malcev–Neumann closure exists). It is unique up to `k[N]`-isomorphism by
Hughes' theorem. Hence `phi`, which carries one Hughes-free embedding to another,
extends.

**Proposition 2.2.** Let `D` be any Hughes-free epic division `k[Gamma]`-ring. Then
`rk_D(B) = d`, hence `rk_D(F) = d` in the free case, and the `D`-analogue of
`d_p - 1` is `0`.

*Proof.* Hughes-freeness for the extension `1 -> N -> Gamma -> Z -> 1` says that the
powers of `t` are left linearly independent over the division closure `D_N` of `k[N]`
in `D`, and conjugation by `t` restricts to an automorphism of `D_N` extending `phi`.
So `D_N[t^{+-1}; phi]` embeds in `D`. It is an Ore domain, and `D` is its division
closure, which is its classical ring of quotients. This twisted polynomial ring also
embeds in `E = D_N((t^-1;phi))`, and the Ore localization maps injectively into `E`.
So `D` is a division subring of `E` containing the entries of `B`. The inner rank of a
matrix over a division ring is unchanged in a division ring extension (Gaussian
elimination). By 2.1, `rk_E(B) = d`. []

## 3. The conditional vanishing and its contrapositive

**Hypothesis MLA(Gamma,p)** (positive-characteristic Lück approximation, as posed
in Jaikin-Zapirain's survey *L2-Betti numbers and their analogues in positive
characteristic*, Groups St Andrews 2017). For every Farber chain `(Gamma_n)` of `Gamma`
and every `A` in `M_{m x l}(k[Gamma])`:
`lim_n null(A_n)/[Gamma:Gamma_n] = m - rk_D(A)`, with `D` the Hughes-free division ring.

**Theorem 3.1.** If MLA(Gamma,p) holds for the single matrix `B`, then
`d_p(Gamma_n)/[Gamma:Gamma_n] -> 0` along every Farber chain.

*Proof.* By 1.2, `(d_p(Gamma_n)-1)/|G_n| <= null(B_n)/|G_n|`. By MLA and 2.2 the right
side tends to `d - d = 0`. []

**Corollary 3.2 (what dies).** Let `(Gamma_n)` be a Farber chain of a free-by-cyclic or
surface-by-cyclic group. Suppose some certificate proves `RG(Gamma,(Gamma_n)) > 0`
through a lower bound `d(Gamma_n) >= d_p(Gamma_n) >= c[Gamma:Gamma_n]`, for one prime or for
the torsion rank of `H_1(Gamma_n;Z)`. Then that certificate refutes MLA for the
matrix `tI - J(phi)` over `F_p[Gamma]`, for some prime `p`.

The integral version needs one more step. `d(H_1(Gamma_n;Z)) = max_p d_p(Gamma_n)`, but
the prime can move with `n`. The certificate therefore refutes the uniform
(in `p`) form of MLA. For one fixed prime it is exactly 3.1.

Characteristic-zero calibration. `b_1(Gamma_n)/[Gamma:Gamma_n] -> b_1^(2)(Gamma) = 0` by Lück's
theorem. So any positive mod-p gradient has to come from `p`-torsion. This agrees with
the note in `fpbs-fg-by-cyclic-farber-chains-bounded-type-reduction`.

Calibration `phi = id`, `N = F_d`. Here `B = (t-1)I`. Over `k[G_n]`, right
multiplication by `t-1` has kernel spanned by the `<t>`-invariant vectors, of dimension
`|G_n|/ord(t_n)` per coordinate. So `null(B_n)/|G_n| = d/ord(t_n)`. In a Farber chain
`ord(t_n) -> infinity`, since `t^j` in `cap Gamma_n` forces `j = 0`. So Theorem 3.1
holds unconditionally here, matching fixed price 1 for `F_d x Z`.

## 4. Unconditional facts along p-layers and for inner type

**Proposition 4.1 (monotone along p-layers).** Suppose `Gamma_n/Gamma_{n+1}` is a
finite `p`-group. Then for every `A` in `M_{m x l}(k[Gamma])`:

    null(A_{n+1})/|G_{n+1}| <= null(A_n)/|G_n|.

In the free case, with `A = F`, this reads
`(d_p(Gamma_{n+1}) - 1)/|G_{n+1}| <= (d_p(Gamma_n) - 1)/|G_n|`.

*Proof.* Put `P = Gamma_n/Gamma_{n+1}`, a normal `p`-subgroup of `G_{n+1}`, and let
`C = coker(. A_{n+1}) = k[G_{n+1}]^l / k[G_{n+1}]^m A_{n+1}`, a left `k[G_{n+1}]`-module.

- Right exactness of the tensor product gives `coker(. A_n) = k[G_n] (x)_{k[G_{n+1}]} C = C/I_P C`,
  where `I_P` is the augmentation ideal of `k[P]`.
- The ring `k[P]` is local with residue field `k`. By Nakayama, `C` is generated over `k[P]`
  by `dim_k(C/I_P C)` elements. So `dim C <= |P| dim(C/I_P C)`.
- Over `k[G]`, `null(A) = (m - l)|G| + dim coker(A)`. Divide by `|G|` and use `|G_{n+1}| = |P||G_n|`. []

So along any refinement by `p`-group layers, the normalized nullity, and in the free case
the mod-p homology gradient, is bounded by its value at the first level of the refinement.
This is the monotonicity the exploratory script `inner2.g` relies on.

**Proposition 4.2 (inner type forbids p-layers at the bottom).** Let `(Gamma_n)` be of inner
type (`Gamma_n N = Gamma`). Then `G_n^ab` is a quotient of `coker(M - I)`, where
`M = phi_ab` acts on `N^ab = Z^d`. In particular, if `det(M - I) = +-1`, every `G_n` is
perfect, and no level of the chain maps onto a nontrivial `p`-group. This holds for the
figure-eight monodromy `a -> ab`, `b -> bab`, where `M - I = [[0,1],[1,1]]`.

*Proof.* `N` surjects onto `G_n`, so `N^ab` surjects onto `G_n^ab`. The relation
`t x t^-1 = phi(x)` holds in `G_n`, where `t` acts by an inner automorphism, hence
trivially on `G_n^ab`. So `(M - I) N^ab` lies in the kernel. []

So for the figure-eight mapping torus, an inner-type counterexample chain cannot start
with a pro-`p` layer at the bottom. Any `p`-layer refinement starts above a perfect
level, as in the PSL_2(q) levels of the exploratory run.

## 5. Numerical check

`experiments/mapping-torus-inner-quotients-2026-09-17/foxnull.g` computes, at the first
inner-type PSL_2(7) and PSL_2(8) levels of the figure-eight mapping torus and for
p = 2, 3, 5, 7:

- `d_p - 1` from the abelian invariants of the kernel;
- `null(F_n)`;
- `null(B_n)`.

It checks the identity `d_p - 1 = null(F_n)` and the bound of 1.2.

Result (`foxnull.out`). In all eight cases `d_p - 1 = null(F_n) <= null(B_n)`:

| level | `p` | `d_p - 1` | `null(F_n)` | `null(B_n)` |
|---|---|---|---|---|
| `PSL_2(7)` | 2 | 31 | 31 | 40 |
| `PSL_2(7)` | 3 | 31 | 31 | 31 |
| `PSL_2(7)` | 5 | 31 | 31 | 31 |
| `PSL_2(7)` | 7 | 32 | 32 | 36 |
| `PSL_2(8)` | 2 | 63 | 63 | 70 |
| `PSL_2(8)` | 3 | 63 | 63 | 64 |
| `PSL_2(8)` | 5 | 62 | 62 | 62 |
| `PSL_2(8)` | 7 | 62 | 62 | 62 |

The normalized nullity `null(B_n)/|G_n|` falls from about 0.18–0.24 at order 168 to about
0.12–0.14 at order 504. This is consistent with Theorem 3.1 but is not evidence for MLA.
