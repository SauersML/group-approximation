# Integer marker with ancillas: exact-read words realize only affine data maps

w7-marker-ancilla, 2026-09-12. Positive route of Family F: is `tau x id` on `1 + k` tracks a
`Z`-equivariant word of track shears, with no blocking? Inputs:
`research/artifacts/marker-stable-formalization-residue-2026-09-12.md` (the Bennett word `A' B A`,
Lemma 2.4) and `marker-flip-cells-avoid-all-marker-control-windows` (ESTABLISHED).

**Result.** Every word whose nonlinear gates read values that do not depend on the ancilla contents
realizes only `F x id` with `F` affine. So a realization of `tau x id` needs a gate whose read value
depends on the ancillas, with that dependence cancelled later. No such word is known, and neither is an
invariant for words of that kind. The hub stays OPEN, and no existing route is invalidated.

## 0. Notation

- `R = F_2[sigma, sigma^(-1)]` acts on `F_2^Z` by shifts. A nonzero `p in R` acts surjectively: solve
  `p v = w` cell by cell in both directions, using the two extreme coefficients.
- Tracks: `s_1` (data) and `s_2, ..., s_n` (ancillas), with `n = 1 + k`. The base point is
  `e = (x, y_1, ..., y_k)`. A word *realizes `F x id`* if `W(x, y) = (F(x), y)` for all Boolean `x, y`.
- A *track shear* is `s_T <- s_T + G(s_i : i != T)`, where `G` is `Z`-equivariant with finite memory.
  It is an involution.

## 1. Audit of Lemma 2.4 (the data track is written twice)

**Statement** (residue artifact, 2.4). Let `W = V_2 o (x += f(z)) o V_1`, where `V_1` and `V_2` do not
write the data track and, for fixed `x`, permute the ancilla configurations. Then `W` does not realize
`tau x id`.

**Check.** The data output is `x + f(z(x, y))`, where `z(x, y)` is the ancilla state after `V_1`. For
fixed `x`, `z` runs over every ancilla configuration as `y` does. So `f(z) = m(x)` for all `z` and all
`x`. Then `m` is constant, while `m(0) = 0` and `m(0010100) != 0`. **PASS.**

**Scope.** The lemma allows arbitrary ancilla automorphisms before the write, but only one data write.
Section 2 allows any number of data writes, but restricts the reads. The two classes are incomparable.

## 2. The linear-dirt invariant

**Definition.** A state is the map `e -> s(e)` on Boolean points. It is *linearly dirty* if
`s = M e + eta(x)`, with `M in GL_n(R)` and each `eta_i` a `Z`-equivariant finite-memory map of `x`
alone. For such a representation, let `c` be the row with `c M = e_1^T` and put
`Q(x) = sum_i c_i(sigma) eta_i(x)`. Then `c s = x + Q(x)`: `Q` is the dirt part of the data functional.

**Moves.**
- (i) *Linear moves.* `s <- E s` with `E in GL_n(R)`: linear shears `s_T += sum_(i != T) p_i s_i`,
  partial shifts and sitewise-linear maps. Also constant translations `s_T += 1`, where `1` is the
  all-ones configuration.
- (ii) *Exact reads.* A track shear `s_T += G(s_i : i != T)` whose read value `G(s_(!= T)(e))`
  depends only on `x`, for all Boolean `e`.

**Theorem.** Let `W` be a word of moves (i) and (ii), with exactness in (ii) judged along the word
starting from `s = e`. If `W` realizes `F x id`, then `F` is affine: `F(x) = p(sigma) x + b`, with `p`
a monomial and `b` constant.

**Lemma A.** If `D in R^(d x d)` has `det D != 0`, then `D` maps `(F_2^Z)^d` onto itself.
*Proof.* `D adj(D) = det(D) I`, and `det D` acts surjectively. Given `w`, pick `v` with
`det(D) v = w`; then `D (adj(D) v) = w`.

**Proof of the theorem.** The invariant is: *`Q` is affine in `x`*.
1. **Start.** `s = e`, so `M = I`, `eta = 0` and `Q = 0`.
2. **Representation independence.** Suppose `M e + eta = M' e + eta'` on all points. Then `(M - M') e`
   depends only on `x`, so `M' = M + d e_1^T` for a column `d`, and `eta' = eta - d x`. Put
   `u = M^(-1) d`. Since `det M' = det M (1 + u_1)`, `1 + u_1` is a unit, and `c' = (1 + u_1)^(-1) c`.
   So `Q' = (1 + u_1)^(-1) (Q - u_1 x)`, that is, `Q' + x = (1 + u_1)^(-1) (Q + x)`. Hence `Q` is
   affine iff `Q'` is.
3. **Linear moves.** `M <- E M`, `eta <- E eta` and `c <- c E^(-1)`, so `Q` is unchanged. A constant
   translation of `s_T` adds `c_T(sigma) 1 = c_T(1) 1`, which is a constant.
4. **Exact reads.** The read value is `g(x) = G(s_(!= T)(x, 0))`, a finite-memory map of `x`. The move
   sends `eta_T <- eta_T + g` and leaves `M` alone, so `Q <- Q + c_T g`.
   - If `c_T = 0`, `Q` is unchanged.
   - If `c_T != 0`, the adjugate formula gives `c_T = (M^(-1))_(1T) = det(M)^(-1) det N`, where `N`
     is `M` with row `T` and column `1` deleted. So `det N != 0`. The other tracks are
     `s_(!= T) = M_(!= T, 1) x + N y + eta_(!= T)(x)`. For fixed `x`, Lemma A lets them run over all
     of `(F_2^Z)^(n-1)`. `G` of them depends only on `x`, so `G` is constant and `g` is a constant.
     `Q` changes by a constant.
   - When `n = 1`, `G` reads no track and is constant.
5. **End.** On a realization, `M e + eta(x) = (F(x), y)` for all `x, y`. Varying `y` with `x` fixed
   shows that the ancilla columns of `M` are `(0; I)`. So `M = [[a, 0], [b, I]]`, and `det M = a` is a
   unit of `R`, hence a monomial. Then `c = (a^(-1), 0, ..., 0)` and `Q = a^(-1) eta_1 = a^(-1) F - x`.
   Since `Q` is affine, so is `F`: `F(x) = p(sigma) x + b`.
6. **Monomial.** Every move is invertible, so `W` is a bijection, and so is `F`. If `p` has at least two
   terms, write `p = sigma^j (p_0 + ... + p_d sigma^d)` with `p_0 = p_d = 1` and `d >= 1`. Then `p v = 0`
   is a recurrence of order `d` that can be solved in both directions from any nonzero initial block.
   So `p` has a nonzero kernel on `F_2^Z`, and `F` is not injective. Hence `p` is a monomial.

**Corollary.** `tau x id` is not realized by such a word, for any `k`. We have `tau(0) = 0`, and
`tau(delta_0) = delta_0`, since a single `1` carries no marker. The only affine map with these values is
the identity, and `tau != id` because it flips the centre of `0010100`.

**Outside the class.**
- **The Bennett word `A' B A`.** `A: y += m(x)` is an exact read and `B: x += y` is linear. After them,
  `M = [[1, 1], [0, 1]]`, `eta = (m, m)`, `c = (1, 1)` and `Q = 0`. The third gate `A'` reads
  `m(x + y + m(x))`, which depends on `y`, so it is not exact.
- **The `4Z` word.** It is only `4Z`-equivariant. Over `F_2[sigma^(±4)]` the data form four tracks, so
  `c` is a `4 x n` matrix. A nonzero entry `c_(jT)` only makes the minor without row `T` and column `j`
  nonsingular. The other three data columns stay fixed with `x`, so step 4 fails and reads of the other
  residue classes are unrestricted.
- **Comparison.** This is a multi-track analogue of
  `formalizable-binary-pairs-over-biorderable-groups-are-affine`, for words rather than formal pairs.
  It is purely functional; no formal computation enters.

## 3. Phase separation, and why it fails

**Scheme** (`k >= 2`: an ancilla `a` and a phase track `p`). For each phase `r = 1, ..., R`:
1. swap `x` and `a` where `psi^(r)(p) = 1`, by `a += x psi; x += a psi; a += x psi`;
2. apply `x_g += phi^(r)_g(p) m_g(a)`, reading the controls from `a`;
3. undo the swap.

Every gate is a track shear. The word realizes `tau x id` if the following hold for every `p` and every
`g`:
- `phi^(r)_g = 1` implies `psi^(r)_g = 0` and `psi^(r)_j = 1` for all `j in C_g`;
- `sum_r phi^(r)_g = 1`.

Later phases see the same markers, by subset stability.

**Failure.** Take `p` constant and `a^0 = 0`. Then `psi^(r)` and `phi^(r)` are `Z`-invariant, so
constant. In each phase with `phi = 1`, one of two things happens:
- `psi = 1`: the flips land on the swapped dirt cell and move into `a`;
- `psi = 0`: the gate adds `m(a^0) = 0` to the data.

So the data output is `x != tau(x)` whenever `x` has a marker.
- **Phases computed from the data** do not help: `p = p^0 + h(x)` runs over every configuration for
  fixed `x`, including the constants.
- **A self-reading gate** `x += phi m(x)` is not a track shear. Treating it as a formal involution would
  need `phi_g phi_j = 0` for `j in C_g`, which fails in the domain `F_2[X]` unless `phi = 0`.

## 4. Borrowed-bit toggling

In reversible circuits, a borrowed bit `a` gives `t += c_1 c_2 c_3` through
`t += a c_3; a += c_1 c_2; t += a c_3; a += c_1 c_2`: the dirt cancels between the two reads. This is
the natural source of cancelling dirt-dependent reads.

**The equivariant analogue.** Use `P: x += y z` (sitewise) and `U: y += L(x)`, with
`L_g = (1 + x_(g-3))(1 + x_(g-2)) x_(g-1)`. Applying `P`, then `U`, then `P`, then `U` sends
- `x -> x + L(x + y^0 z^0) z^0`;
- `y -> y^0 + L(x + y^0 z^0) + L(x + L(x + y^0 z^0) z^0)`.

**Why it fails.** The toggle needs `U` to read the same controls twice, but the dirty write `y^0 z^0`
first moves data cells inside other windows. At `y^0 = 0` and `z^0 = 1`, the word flips every cell that
follows a `001` and leaves the garbage `L(x) + L(x + L(x))` on `y`. Starting with `U` instead gives the
symmetric failure `x -> x + L(x + y^0 z^0 + L(x) z^0) z^0`. The circuit identity does not transfer as
written, because the controls of one marker are the targets of others.

## 5. Checks that give no obstruction

- **Finite and not equivariant.** On a finite window, the cell gates `x_i += m_i(x_(C_i))`, applied one
  cell at a time in any order, realize `tau` by subset stability. The difficulty is only simultaneous
  equivariant writes.
- **Orbit sign on periodic points.**
  - Prime periods: the sign is even for `tau x id` and for track shears (earlier check).
  - Period 6: a marker at `i` forces `x_(i+1..i+5) = 1,0,0,0,1`, so the marked 6-periodic points are the
    shifts of `010001` and `110001`. `tau` swaps these two orbits, so `sign_6(tau) = 1` on one track.
    With `k >= 1` ancillas there are `2^(6k+1)` moved orbits, so `sign_6(tau x id) = 0`.
    Stabilization kills this sign.
  - Composite periods beyond 6 were not checked.
- **Torsion-free invariants** (the dimension representation and similar) vanish on involutions, and
  `tau x id` and every track shear are involutions.

## 6. Where it stops

- **Positive.** A realization must contain a read whose value depends on the ancilla contents, and must
  cancel that dependence later. The phase and toggle schemes of Sections 3–4 fail as written.
- **Negative.** A proof must control states that are nonlinear in the dirt, where `Q` is undefined. It
  must still allow the `4Z` word, as Section 2 does.
- `injective-binary-automata-are-stably-formalizable` and
  `one-ancilla-marker-residue-is-supported-on-window-overlaps` stay OPEN.

## 7. Verification record

- Sections 1–5 were derived by w7-marker-ancilla.
- **PASS** by w3-vf-nonlinear at e0c1d6277f (verification artifact, Section 30). It re-derived:
  - steps 2–5 and Lemma A;
  - the corollary, the Bennett-word computation, the `4Z` remark and the Lemma 2.4 audit.
  Its duplicate scan found no node that states or implies the claim.
- **Follow-up to its two notes.**
  - Step 6 adds the bijectivity argument for "p a monomial". Steps 1–5 give only "affine", and the
    corollary needs only that.
  - The claim node now says that constant translations add a constant to `Q`.
