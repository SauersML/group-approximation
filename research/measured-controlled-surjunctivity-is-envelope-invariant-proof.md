---
rg: 2
id: measured-controlled-surjunctivity-is-envelope-invariant-proof
kind: route
title: Induce the automaton to the envelope along clopen fundamental domains and read it back on the other lattice slot by slot
target: measured-controlled-surjunctivity-is-envelope-invariant
requires: []
---

The notation is that of the target. `Gamma` acts on `A^Gamma` by `(g.c)(k) = c(g^-1 k)`. The
automaton `Psi` has memory `S` and a finite clopen partition `P` of `Y`, and
`psi_y(c)(k) = F(cell(k^-1 y), (c(k s))_(s in S))` for a fixed local rule `F`. The only inputs are
the existence of left Haar measure and the formula `m(Eg) = Delta(g) m(E)`, with `Delta = 1` by
unimodularity.

## Step 0: two subgroups and two fundamental domains

**Small subgroup.** Since `Gamma` and `Lambda` are discrete, some compact open subgroup `W` meets
`Gamma` only in `1`. Then each left coset `gW` contains at most one point of each coset `h Gamma`:
if `h gamma, h gamma'` lie in `gW`, then `gamma^-1 gamma' in W`, so `gamma = gamma'`.

**Clopen fundamental domains.**
- The quotient map `p : H -> H/Gamma` is open.
- `p` is injective on every `gW`, so `p(gW)` is compact open.
- By compactness of `H/Gamma`, finitely many `p(g_i W)` cover it. Put
  `E_i = p(g_i W) \ (E_1 u ... u E_(i-1))`, which is clopen.
- Then `D = u_i (g_i W ∩ p^-1(E_i))` is compact open, and `H = ⊔_(gamma) D gamma`.

For the left action of `Lambda`, choose `W` so that it also meets `Lambda` only in `1`. Then the
quotient `H -> Lambda\H` is injective on right cosets `Wg`, and the same construction with right
cosets gives a compact open `D'` with `H = ⊔_(lambda) lambda D'`.

Each point `x` of `D'` has a compact open subgroup `W_x` with `x W_x ⊆ D'`. Finitely many
`x_i W_(x_i)` cover `D'`. Replacing `W` by `W ∩ ⋂_i W_(x_i)` keeps `W ∩ Gamma = 1` and makes each
`x_i W_(x_i)` a union of left `W`-cosets. So `D' = d_1 W ⊔ ... ⊔ d_K W`.

**Memory subgroup.** Put `V = W ∩ (⋂_(s in S) s W s^-1)`, a compact open subgroup. If
`q, q'` lie in one coset `gV`, then for every `s in S` the points `qs, q's` lie in one coset
`gsW`: indeed `q' = q v` with `v in V`, so `q's = qs (s^-1 v s)`, and `s^-1 v s in W`.

## Step 1: the induced base

- `Gamma` acts on `H x Y` freely and properly, so `Z = (H x Y)/Gamma` is Hausdorff and the quotient
  map `pi` is open.
- The map `D x Y -> Z` is a continuous bijection from a compact space, hence a homeomorphism.
- So `Z` is compact, metrizable and zero-dimensional.
- For compact open `C` in `H` and clopen `Q` in `Y`, the image `pi(C x Q)` is open and compact,
  hence clopen.

**Fibres.** The fibre of `z = [h, y]` is `A^(h Gamma)`, where `h Gamma` is a subset of `H`. On it
`psi_z(c)(h k) = F(cell(k^-1 y), (c(h k s))_s)` for `k in Gamma`.

- *Well defined.* Replace `(h, y)` by `(h g, g^-1 y)`. The site `h k` is `(h g)(g^-1 k)`, and
  `cell((g^-1 k)^-1 g^-1 y) = cell(k^-1 y)`.
- *Conjugate to `psi_y`.* The bijection `Gamma -> h Gamma`, `k -> h k`, conjugates `psi_z` to
  `psi_y`. So `psi_z` is injective and not surjective, for every `z`.
- *Equivariant.* For `lambda in Lambda`, left multiplication `h Gamma -> lambda h Gamma` carries
  `psi_z` to `psi_(lambda z)`.

## Step 2: slots

Put `B = A^K`. For `z = [h, y]` and `(lambda, j)` in `Lambda x {1..K}`, the slot `(lambda, j)` is
**occupied** if `h Gamma` meets `lambda d_j W`; its point `q_z(lambda, j)` is then unique by
Step 0. Since `H = ⊔ lambda d_j W`, the occupied slots biject with `h Gamma`.

**Coordinates.** Define `Theta_z : B^Lambda -> A^(h Gamma) x A^(unoccupied slots)` by reading
occupied slots as the value at their point. It is a bijection, and it is equivariant:
`Theta_(lambda z)(lambda . b) = lambda . Theta_z(b)`. This is because
`q_(lambda z)(lambda mu, j) = lambda q_z(mu, j)`.

**New fibre maps.** Put `tau_z = Theta_z^-1 o (psi_z x id) o Theta_z`. Each `tau_z` is injective
and not surjective, and `tau_(lambda z) o lambda = lambda o tau_z`.

## Step 3: the new automaton is local and controlled

Put `L = { mu in Lambda : mu D' meets D' S }`. `D' S` is compact and the sets `mu D'` are disjoint
and open, so `L` is finite. Define `Phi(b, z) = (tau_z(b), z)` on `B^Lambda x Z`. Coordinate `j`
of `tau_z(b)(e)` is computed as follows.

- **Unoccupied slot `(e, j)`.** The value is `b(e)_j`.
- **Occupied slot, with point `q = h k` in `d_j W`.** The value is
  `F(cell(k^-1 y), (b(mu_s)_(i_s))_(s in S))`, where `q s in mu_s d_(i_s) W`. Here `mu_s in L`, and
  by Step 0 the pair `(mu_s, i_s)` depends only on the coset `qV`.

**The control partition.** For each `j`, the sets `N_j = Z \ pi(d_j W x Y)` and
`Z_(j, gV, Q) = pi(gV x Q)` together partition `Z`. Here `gV` ranges over the finitely many
`V`-cosets inside `d_j W`, and `Q` over the cells of `P`.

- These sets are clopen by Step 1.
- `z` lies in `Z_(j, gV, Q)` exactly when slot `(e, j)` is occupied, its point lies in `gV`, and
  the `Y`-coordinate `k^-1 y` of the unique representative `[q, k^-1 y]` lies in `Q`.
- On each cell of the common refinement over `j = 1..K`, all the data above is constant. So
  `tau_z(b)(e)` depends only on `b|_L` and on that cell.
- By Step 2, `Phi` commutes with `Lambda`, so the value at `lambda` is read at `lambda^-1 z`.

`Phi` is therefore a `Z`-controlled automaton over `B`. All its fibre maps are injective and none
is surjective. This proves part 1.

## Step 4: the invariant measure

Let `m` be Haar measure. Let `mu` be the image of `(m|_D / m(D)) x nu` under the homeomorphism
`D x Y -> Z`.

**Invariance.** Fix `lambda in Lambda`. For each `gamma`, put `D_gamma = D ∩ lambda^-1 D gamma`.
- Only finitely many `D_gamma` are nonempty, since `lambda D` is compact, and they partition `D`.
- On `D_gamma x Y`, `lambda` acts in coordinates by
  `(d, y) -> (lambda d gamma^-1, gamma y)`, because `[lambda d, y] = [lambda d gamma^-1, gamma y]`.
- This map preserves `m x nu`: it uses left invariance of `m`, `Delta(gamma^-1) = 1`, and
  `Gamma`-invariance of `nu`.
- The images `D ∩ lambda D gamma^-1` partition `D`, since `H = ⊔_gamma lambda D gamma^-1`.

So `lambda` preserves `mu`.

**Full support.** Haar measure charges nonempty open sets and `nu` has full support, so `mu` has
full support. This proves part 2.

## Step 5: invariance and consequences

**Invariance.** The hypotheses are symmetric in `Gamma` and `Lambda`.
- A strict controlled automaton for `Lambda` over a base with an invariant probability of full
  support induces, by parts 1 and 2 with the roles exchanged, one for `Gamma`.
- So `Gamma` MCS implies `Lambda` MCS, and conversely. This proves part 3.

**MCS gives surjunctivity.** A one-point base carries its Dirac measure. A strict cellular
automaton is a strict controlled automaton over it, so MCS implies surjunctivity. For
`Y = point`, `Z = H/Gamma` with Haar probability. This proves part 4.

**Discrete `H`.** Take `W = {1}` and counting measure.
