# Clifford covers of the Kun--Thom wreath: bounded-block models kill the center

Lane `ex-q34-kt-wreath-soft-kernel`, 2026-09-13, part 4.  Uses part 3,
Theorem 9 (`research/artifacts/ex-q34-kt-wreath-soft-kernel-part3-2026-09-13.md`):
every homomorphism `W -> prod_omega (U(k) wr S_n)` kills `K_even`.  Everything
is proved here.  Nothing was run.  Unreviewed.

## 0. Summary

Let `S` be a `G`-invariant graph on `X = G/Gamma` containing the Kun--Thom marked
pair `{o, y}`, with `o = Gamma`, `y = h Gamma`, `h = t^(-1) gamma t notin Gamma`,
so that the marked word survives.  Since `h in N`, this pair lies inside an
`N`-fibre.  Let `Wtilde_S = Vtilde_S x| G` be the Clifford cover of
`invariant-graph-clifford-phase`: `Vtilde_S` is the central `F_2`-extension of
`V = F_2[X]` with `z` central, `c_u^2 = 1` and `[c_u, c_v] = z^(b_S(u, v))`.
These covers include the minimal nonsofic quotients of
`H = G *_Gamma (Gamma x C_2)` in which the Kun--Thom marked word survives.
Their lamp algebra at `z = -1` is noncommutative, so the soft kernel of a
bounded-block model could be a nonabelian locally finite group.  This is the
one place where Pauli-type internal blocks might have helped.

**Theorem 12.**  For every fixed `k`, every homomorphism
`rho : Wtilde_S -> prod_omega (U(k) wr S_n)` kills `z` and the full preimage
`Ktilde_even` of `K_even`.  In particular `Wtilde_S` has no regular HS model in
`U(k) wr S_n`, and no regular microstates approximately permuting a
bounded-rank frame.

The proof tensors the model with its conjugate.  That kills the sign, and
Theorem 9 then makes the fibre-even lamps scalar.  Scalars commute, while the
invariant graph forces two fibre-even lamps to anticommute.

## 1. Two elementary identities

For a unitary `X in M_k` with `tr = Tr/k`,

```text
||X - tr(X) 1||_2^2 = 1 - |tr X|^2,        ||X ⊗ conj(X) - 1||_2^2 = 2 - 2 |tr X|^2.     (SC)
```

The first expands `tr((X - t)^*(X - t))` with `t = tr X`.  The second uses
`tr(X ⊗ conj X) = |tr X|^2`.  For block-diagonal `X = (X_i)` over `[n]`, apply
(SC) blockwise and average over pairs `(i, j)`.  Then
`||X ⊗ conj(X) - 1||_2 -> 0` along `omega` forces
`(1/n^2) sum_(i,j) |tr X_i conj(tr X_j) - 1|^2 -> 0`, hence
`|tr X_i| -> 1` on most blocks with a common value of `tr X_i` up to `o(1)`.
So `X` is `L^2`-close to one scalar `lambda 1`.

## 2. The invariant graph pairs two fibre-even lamps oddly

**Lemma 13.**  If `S` has an edge `{o, y}` inside one `N`-fibre `F`, there are
`u, v in K_even`, supported in `F`, with `b_S(u, v) = 1`.

*Proof.*  Suppose `b_S(u, v) = 0` for all `u, v in K_even` supported in `F`.
Take `u = e_o + e_a` and `v = e_y + e_c`, with `a, c in F`:

```text
1_S(o, y) + 1_S(o, c) + 1_S(a, y) + 1_S(a, c) = 0.
```

With `a = c` this gives `1_S(o, a) + 1_S(a, y) = 1` for `a notin {o, y}`.  Put
`f(a) = 1_S(o, a)`.  Then `1_S(a, c) = f(a) + f(c)` for `a != c`.  So the edges
of `S` inside `F` form the cut of `A = {f = 1}` and its complement.
`S` is `N`-invariant and `N` preserves `F`, so every `n in N` maps `A` to `A` or
to `F \ A`.  This defines a homomorphism `N -> Z/2`, trivial because
`N = EL_r(R)` is perfect.  So `A` is `N`-invariant.  `N` acts transitively on
`F`, so `A = ∅` or `A = F`, and `S` has no edge inside `F`.  Contradiction.  ∎

## 3. The theorem

*Proof of Theorem 12.*
- *Corners.*  `rho(z)` is a self-adjoint unitary commuting with
  `rho(Wtilde_S)`, and it is block-diagonal, since `z` lies in `Rad_sof`.
  Its spectral projections `p_± = (1 ± rho(z))/2` are block-diagonal and
  invariant.  `rho(g)` maps the range of `p_-` in block `i` onto its range in
  block `psi(g) i`, so the rank `r_i` of `p_-` in block `i` is
  `psi`-invariant.  Restrict to the `psi`-invariant set `Y_r = {i : r_i = r}`,
  `1 <= r <= k`, of positive measure.  On the range of `p_-` this gives a
  block-monomial model `rho_r` of block size `r` with `rho_r(z) = -1`.
- *Tensor square.*  `rho_r ⊗ conj(rho_r)` is a block-monomial model of block
  size `r^2`, over `Y_r × Y_r`.  It sends `z` to `1`, so it factors through
  `Wtilde_S / <z> = W`.  By Theorem 9 it kills `K_even`.  So for every
  `utilde in Ktilde_even`, `rho_r(utilde) ⊗ conj(rho_r(utilde)) = 1`, and by
  (SC) `rho_r(utilde) = lambda(utilde) 1` is a scalar.
- *Contradiction.*  Take `u, v` from Lemma 13 with lifts `utilde, vtilde`.
  Scalars commute, so `rho_r(z) = rho_r([utilde, vtilde]) = 1`.  But
  `rho_r(z) = -1`.  So every `Y_r` is null, `p_- = 0` and `rho(z) = 1`.
- *Descent.*  Now `rho` factors through `W`, and Theorem 9 kills `K_even`.
  Hence `rho(Ktilde_even) = 1`.  ∎

The step "`z` lies in `Rad_sof`" is used only to make `rho(z)` block-diagonal.
It holds because the image of `z` in any sofic group is trivial: `z` is the
marked word's image when `{o, y}` in `S` (`invariant-graph-clifford-phase`
item 2), and `x in Rad_sof(H)`.  Without it the corner argument still runs
after replacing `p_±` by the spectral projections of `rho(z)` in `rho(W)'`,
but block-diagonality is then not automatic.  So the theorem is stated for
graphs containing the marked pair, or any pair `{o, y}` whose word survives.

## 4. Scope

- Same trust surface as part 3 (Kun--Thom 4.1 via
  `normal-closure-fixes-gamma-fixed-algebra`).
- Unbounded block size is not covered.  The hyperfinite model `A_S x| G` of
  `invariant-graph-clifford-phase` item 3 is a tracial model with unbounded
  Clifford blocks, as it must be.
- Nothing here says `Wtilde_S` is not hyperlinear.
