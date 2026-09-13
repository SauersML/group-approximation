# Characters of the pure braided Brown–Higman–Thompson groups bF_{n,r}

Lane z2-13-pure-braided-bht, 2026-09-13. Unreviewed. Part 1: the character group and the full-twist
functional. Part 2 (`zp-pure-braided-bht-sigma-2026-09-13.md`): consequences for Sigma^m.

## 0. Setup

Fix `n >= 2`, `r >= 1`, `d = n - 1`. `A = Z[1/n]`. A *standard interval* is `[a, a + n^{-e}]` with `a` in `A`,
`e >= 0`. An `n`-ary forest with `r` roots and `k` leaves is the same thing as a subdivision of `[0, r]` into
`k` standard intervals obtained from `[0,1], ..., [r-1, r]` by repeated `n`-fold splitting; `k ≡ r mod d`.

`bF_{n,r}` = classes of `(T_-, b, T_+)`, `T_±` forests with `r` roots and `k` leaves, `b` in `PB_k`, modulo
expansion: splitting leaf `i` in both forests and cabling strand `i` of `b` into `n` parallel strands.
`pi: bF_{n,r} -> F_{n,r}` forgets `b`; `s(T_-, T_+) = (T_-, 1, T_+)` is a section. So
`bF_{n,r} = N ⋊ F_{n,r}` with `N = ker pi = union over forests T of PB(T) = {(T, b, T)}`.

For a split extension `N ⋊ Q`: `Hom(N ⋊ Q, R) = Hom(Q, R) ⊕ Hom(N, R)^Q` (a `Q`-invariant homomorphism on `N`
extends by zero on `s(Q)`; conversely restrict). So

`Hom(bF_{n,r}, R) = pi^* Hom(F_{n,r}, R) ⊕ W`, `W := Hom(N, R)^{F_{n,r}}`.

`Hom(F_{n,r}, R)` has rank `n` (Brown 1987, Stein 1992; for `r = 1` this is `F_{n,infinity}`, basis
`chi_0, psi_0, ..., psi_{n-3}, chi_1` in Zaremsky arXiv:1502.02620). The new content is `W`.

## 1. Residues

**Lemma 1 (residue).** The map `res: A -> Z/d`, `x -> x·n^K mod d` (any `K` with `x n^K` in `Z`), is a
well-defined additive map with kernel `dA`, and `res(n^{-e}) = 1`. A PL homeomorphism with slopes in `<n>`
and breakpoints in `A` satisfies `res(g(x) - g(y)) = res(x - y)` for `x, y` in `A`.

*Proof.* `n ≡ 1 mod d`, so multiplying by `n` does not change the class mod `d`. `g(x) - g(y)` is a sum of
`n^{k_i} l_i` with `sum l_i = x - y`, and `res(n^{k_i} l_i) = res(l_i)`. ∎

So in a forest with `k` leaves, leaf `i` (counted from the left) has left endpoint of residue `i - 1`.

**Lemma 2 (matching gaps).** Let `[u, v]`, `[u', v']` have endpoints in `A` and positive length. There is a
PL homeomorphism `[u, v] -> [u', v']` with slopes in `<n>` and breakpoints in `A` iff
`res(v - u) = res(v' - u')`.

*Proof.* Necessity: Lemma 1. Sufficiency: subdivide `[u, v]` into standard intervals; the number of pieces
is `≡ res(v - u) mod d`, and splitting one piece raises it by `d`. Do the same for `[u', v']`, raise both
counts to a common value `N`, and map piece `t` affinely onto piece `t`; slopes are powers of `n`. ∎

## 2. Types of leaf pairs

Let `I < J` be two leaves of a forest (standard intervals, `I` to the left). Record the three gaps:
`A` = `[0, left(I)]`, `G` = `[right(I), left(J)]`, `B` = `[right(J), r]`. Each gap is either **E**xact (length
zero) or **P**ositive with a residue in `Z/d`. Since `res(I) = res(J) = 1`, the residues satisfy
`res(A) + res(G) + res(B) + 2 ≡ r`, so a *type* is `(A, G, B)` with `B`'s residue determined. In index form,
for leaves `i < j` of a forest with `k` leaves:

- `A` exact iff `i = 1`, else residue `alpha = i - 1`;
- `G` exact iff `j = i + 1`, else residue `gamma = j - i - 1`;
- `B` exact iff `j = k`, else residue `k - j`.

**Lemma 3.** Two leaf pairs `(I, J)` of forests `U`, `(I', J')` of `U'` have the same type iff some
`g` in `F_{n,r}` maps `I` affinely onto `I'` and `J` affinely onto `J'`.

*Proof.* "If": exactness is preserved by homeomorphisms, residues by Lemma 1. "Only if": map the three gaps by
Lemma 2 (exact gaps stay points) and `I`, `J` affinely; the glued map is a PL homeomorphism of `[0, r]` with
slopes in `<n>` and breakpoints in `A`, i.e. an element of `F_{n,r}`, representable by a forest pair whose
leaves include `I`, `J` and `I'`, `J'`. ∎

## 3. The invariant characters `W`

`H_1(PB_k)` is free abelian on the classes `A_{ij}`, `i < j`. `H_1(N) = colim_T H_1(PB(T))`. Expanding leaf `i`
cables strand `i`, so `A_{ij} -> sum_{s=1}^n A_{i_s j}` in `H_1` (same for `A_{ji}`), other generators unchanged.
Conjugation by `s(T_-, T_+)` sends the braid on the leaves of `T_+` to the same braid on the leaves of `T_-`.
Hence (Lemma 3) `W` = functions `phi` on types satisfying, for every type `(A, G, B)`:

- (RI) `phi(A, G, B) = sum_{s=1}^{n} phi(A_s, G_s, B)`, where `A_1 = A`, `A_s = P(res A + s - 1)` for `s >= 2`,
  `G_n = G`, `G_s = P(res G + n - s)` for `s <= n - 1` (split `I` into `n` pieces);
- (RJ) `phi(A, G, B) = sum_{t=1}^{n} phi(A, G_t, B_t)`, where `G_1 = G`, `G_t = P(res G + t - 1)` for `t >= 2`,
  `B_n = B`, `B_t = P(res B + n - t)` for `t <= n - 1` (split `J`).

Write the types as `PPP(alpha, gamma)`, `EPP(gamma)`, `PPE(alpha)`, `PEP(alpha)`, `EPE`, `EEP`, `PEE`, `EEE`
(letters = exactness of `A, G, B`; residues not forced by the constraint are shown).

**Theorem 1.** `dim W = n(n - 1)`. Explicitly, `phi` in `W` is determined by free data

- `PPP: (Z/d)^2 -> R` with every row sum `sum_gamma PPP(alpha, gamma)` zero and every antidiagonal sum
  `sum_alpha PPP(alpha, k - alpha)` zero: dimension `(d - 1)^2`;
- `EPP: Z/d -> R` with sum zero: `d - 1`; `PPE: Z/d -> R` with sum zero: `d - 1`;
- `PEP: Z/d -> R` arbitrary: `d`; `EPE` in `R`: `1`;

and then `EEP = EPP(0) + PEP(0) - PPP(0, 0)`, `PEE = PEP(r-2) + PPE(r-2) - PPP(r-2, 0)`,
`EEE = EEP + EPE - EPP(0)` (when that type occurs). Total `(d-1)^2 + 2(d-1) + d + 1 = d^2 + d = n(n-1)`.
So `Hom(bF_{n,r}, R)` has rank `n + n(n - 1) = n^2`.

*Proof.* Expanding the relations (in each, the terms `s = 1` and `s = n`, resp. `t = 1`, `t = n`, reproduce a
type of the same residues; `s - 1 = j` runs over `1..d-1` in the middle):

1. RI on a type with `G` positive gives `sum_{all alpha'} phi(P alpha', P(k - alpha'), B) = 0` for fixed
   `k = res A + res G` and fixed `B`. With `B` positive: antidiagonal sums of `PPP` vanish. With `B` exact:
   `sum PPE = 0`.
2. RJ on a type with `G` positive (either `B`) gives `sum_{gamma'} phi(A, P gamma', P(.)) = 0` for fixed `A`:
   row sums of `PPP` vanish, and `sum EPP = 0`.
3. RI with `G` exact, `A` positive and RJ with `G` exact reproduce 1–2. RI with `A` exact, `G` exact, `B`
   positive gives `EEP = EPP(0) + PEP(0) + sum_{j=1}^{d-1} PPP(j, -j)`, and by 1 this is
   `EPP(0) + PEP(0) - PPP(0,0)`. RJ with `A` positive, `G`, `B` exact gives the `PEE` formula via 2. RI and RJ
   on `EEE` give two formulas for `EEE`; substituting the others they agree.
4. No relation involves `PEP` or `EPE` except through the derived formulas, so those are free.

For the `PPP` count: over `C`, Fourier transform on `(Z/d)^2`; row sums zero kill `P^(chi, 1)`, antidiagonal
sums zero kill `P^(chi, chi)` for all `chi`; the two families overlap exactly at `(1, 1)`, so they impose
`2d - 1` independent conditions. ∎

**Check `n = 2`** (`d = 1`): `W` has the free parameters `PEP` (adjacent strands) and `EPE` (first and last
strands), matching `omega_1`, `omega_0` and `F_br^{ab} = Z^4` (Zaremsky arXiv:1403.8132 Lemma 1.7).

**New for `n = 3`** (`d = 2`): `dim W = 6`. Example: `PPP(alpha, gamma) = (-1)^gamma`, i.e.
`A_{ij} -> (-1)^{j-i-1}` for non-adjacent interior leaves, with `EEP = PEE = -1` and the other data zero.
It is invariant under ternary splitting because a leaf splits into three pieces whose gaps to `J` have
parities `gamma, gamma + 1, gamma`: `(+1) + (-1) + (+1) = +1`.

## 4. The full-twist functional

For a forest `S` with `k` leaves let `z_S = (S, Delta_k^2, S)`, the full twist on all strands. By §2 the
types of the pairs `(i, j)` depend only on `(i, j, k)`, so `tau_phi(k) := phi(z_S) = sum_{i<j} phi(type(i,j,k))`
depends only on `k`.

**Proposition 2.** On `k >= 3`, `k ≡ r mod d`, `tau_phi(k) = tau_0 + c k` is affine. The map
`W -> R^2`, `phi -> (tau_0, c)` is onto, so `W_0 := {phi : tau_phi(k) = 0 for all large k}` has dimension
`n(n-1) - 2`, which is positive for `n >= 3` and zero for `n = 2`.

*Proof.* Cabling strand `i` of `Delta_k^2` gives `Delta_{k+d}^2 · (Delta^2_{block})^{-1}` (commuting), so
`tau(k + d) - tau(k) = phi((S', Delta^2_{block}, S'))`. For `k >= 3` choose an interior leaf `i`; the internal
pairs of the block have types that depend only on residues (not on `k` beyond `k mod d`), so the increment is
a constant `c d`. Onto: `EPE = 1` (other free data zero) gives `tau ≡ 1`; `PEP ≡ 1` gives `EEP = PEE = 1` and
`tau(k) = k - 1`. ∎

For `n = 2` this is `tau(k) = omega_0 + (k - 1) omega_1`, the value `c + (n-1)d` used in Zaremsky's Theorem 5.1
proof (arXiv:1803.02717). For `n >= 3` the subspace `W_0` is invisible to every full twist.
