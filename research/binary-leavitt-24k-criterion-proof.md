---
rg: 2
id: binary-leavitt-24k-criterion-proof
kind: route
title: Round the two finite factors to exact regular form, and recover separation by tensor amplification
target: binary-leavitt-hyperlinear-iff-24k-feasible
requires:
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
  - binary-leavitt-elementary-group-is-simple
artifacts:
  - research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md
---

## Proof

Throughout, `||A||_(2,d)^2 = tr_d(A^*A)` with `tr_d = d^(-1) Tr`, and a word
of length `l` in unitaries changes by at most `l epsilon` when each letter
moves by `epsilon` (telescoping; unitary factors do not change the norm of a
summand).

**A finite computable exhaustion.** For `m>=1`, use exactly the bounded
word-and-certificate definition of `T_m` in the target, with the fixed
kernel word `r_*` explicitly adjoined. There are finitely many reduced
free-product words of at most `m` syllables, since both factors are finite.
There are also finitely many certificates consisting of at most `m`
terms `a p_i b`, with `p_i` one of the five defining ring polynomials and
`a,b` monomials of length at most `m`. Equality of two free noncommutative
polynomials over `F_2` is decidable by collecting monomials. Thus membership
in this bounded set is computable. The sets are nested, and every kernel
word eventually belongs, since every one of its nine entries has some
finite ideal certificate. The constant-root calculation in the generation
proof gives `q(r_*)=1`, so the explicitly adjoined word is also in `N`.

The word-length bound repairs an actual defect in the previous formulation.
The words `(b_1 c b_1 c^(-1))^(4j)`, `j>=1`, are distinct in the free
product, but their matrices are already identity over the free
characteristic-two coefficient algebra: `(x_12(s_0)x_23(s_0))^4=I`.
All their entries therefore have zero certificates, regardless of word
length. Certificate bounds alone would give infinite sets. This correction
changes no step of the equivalence below.

**Feasibility implies hyperlinear.**  Choose `k_m, U_m` with error below
`1/m` on `T_m` and set `pi_m = pi_(k_m,U_m)`.  Each `pi_m` is an exact
representation of `P`, and by the exhaustion every fixed element of `N` is
sent to the identity asymptotically, so the sequence induces a homomorphism
`rho` from `H = P/N` into the unitary group of the tracial matrix
ultraproduct.  `rho(c) != 1` because `tr(C_k) = 0` gives
`||C_k - I||_2 = sqrt 2`.  The kernel of `rho` is a proper normal subgroup of
the simple group `EL_3(R)` (second prerequisite), hence trivial.

For the finite-model form of separation, pick a word `w_g` for each `g in H`
with `w_1 = 1` and set `V_m(g) = pi_m(w_g)`; the error words
`w_g w_h w_(gh)^(-1)` lie in `N`, so these are approximately multiplicative
on every fixed finite set.  For `g != 1`, injectivity gives
`l_g = ||rho(g) - I||_2 > 0`.  Given a finite `F`, along ultrafilter-many
indices `||V_m(g) - I||_2 > l/2` for all `g in F \ {1}` with
`l = min_g l_g`.  For a unitary `V` with `tr V = z`,

```text
||V - I||_2^2 = 2 - 2 Re z,       |(1+z)/2|^2 <= (1 + Re z)/2,     (LK5)
```

so `||V - I||_2 >= gamma` makes `|(1+z)/2|^2 <= 1 - gamma^2/4 < 1`.  Replacing
each `V` by `(I (+) V)^(tensor r)` multiplies the normalized trace to
`((1+z)/2)^r` and multiplies the multiplicative error by at most `r`; choose
`r` with all these traces below `1/2` in modulus, then an index with error
below the tolerance divided by `r`.  The amplified maps satisfy
`||(I (+) V)^(tensor r) - I||_2^2 = 2 - 2 Re(trace) > 1`, so the single
constant `1` works for every finite set and every tolerance.

**Hyperlinear implies feasibility.**  Take models of `H` and pull them back
along the generators `(LG1)`; every fixed word of `N` then tends to the
identity.  Three corrections put them in the form `(LK2)`.

*Canonical traces.*  With `(LK5)`, the amplification `V -> (I (+) V)^(tensor r)`
drives `tr(phi(g))` to `0` for each `g != 1` in a prescribed finite set while
multiplying the multiplicative error by at most `r`; a diagonal choice over an
increasing exhaustion gives models with vanishing traces off the identity.
The finite factors `A` and `B` inject into `H` by the first prerequisite, so
their characters converge to the regular characters.

*Exact finite factors.*  Round the eigenvalues of the image of `c` to cube
roots of unity and those of each `b_i` to signs; on the unit circle the
distance to the nearest cube root is bounded by `|z^3 - 1|` and to the nearest
sign by `|z^2 - 1|`, so the change is bounded by the corresponding relation
defect.  The resulting `T` are self-adjoint involutions commuting up to
vanishing errors; make them commute one at a time by averaging

```text
A = 2^(-(j-1)) sum_(eps) S_1^(eps_1) ... S_(j-1)^(eps_(j-1)) T
                          S_(j-1)^(eps_(j-1)) ... S_1^(eps_1),
```

a self-adjoint contraction commuting with `S_1,...,S_(j-1)` with
`||A - T||_2 -> 0`, hence `||A^2 - I||_2 <= 2||A - T||_2`; then
`S_j = sign(A)` satisfies `||S_j - A||_2 <= ||I - A^2||_2` because
`1 - |a| <= 1 - a^2` on `[-1,1]`.  Three generators, three steps.

*Exactly regular multiplicities.*  For a finite abelian `K` the character
projections are `P_chi = |K|^(-1) sum_g conj(chi(g)) rho(g)`, so vanishing
traces off the identity give `tr(P_chi) -> 1/|K|`.  Amplify the tuple
24-fold, so the target multiplicities `D/3` and `D/8` are integers, and
relabel characters on surplus basis vectors; the relabelled fraction is
`(2D)^(-1) sum_chi |dim P_chi - D/|K||` which tends to zero, and each
generator moves by at most four times that in squared normalized HS norm.
Doing this for the two factors separately makes each exactly a multiple of
its regular representation, while all previously small word errors stay small.

Finally, a global unitary conjugacy puts the first factor in the form `C_k`,
and matching simultaneous eigenspaces of equal multiplicities gives one
unitary `U` with the second factor equal to `U D_(i,k) U^*` for all three `i`
at once.  Every fixed relation still tends to the identity, so `Delta_m = 0`
for every `m`.
