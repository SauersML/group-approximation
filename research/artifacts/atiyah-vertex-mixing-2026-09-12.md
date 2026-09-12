# Vertex-mixing matrices over a Kazhdan edge: the Cohn-coproduct reduction

Lane `atiyah-vertex-mixing`, 2026-09-12. Target: the open part of Strong Atiyah over an
amalgam `G = A *_C B` with an infinite property (T) edge `C`, after
`atiyah-amalgam-unmixed-matrices-reduce-to-factors` (matrices supported in one vertex or in the
edge are integral) and `atiyah-kazhdan-edge-blocks-both-permanence-routes` (Lück's
amenable-edge flatness and Jaikin-Zapirain's Hughes-free framework both fail at a (T) edge).

**Outcome.** The vertex-mixing case is not decided. What is proved is an elementary reduction:
integrality of every von Neumann rank over `G` follows from integrality of one explicit rank
function on the ring coproduct `R = D_A *_(D_C) D_B` of the vertex division closures over the
edge division closure, and in particular from equality of that rank function with the inner
rank of `R`. This relocates the open problem from matrices over `K[G]` to the single ring
homomorphism `phi: R -> U(G)`.

## Setting and notation

- `K` is a subfield of `C` closed under complex conjugation.
- For a group `H`, `N(H)` is the group von Neumann algebra and `U(H)` its algebra of affiliated
  operators. For `H <= G` there are unital inclusions `N(H) <= N(G)` and `U(H) <= U(G)`.
- `D_H` is the division closure of `K[H]` in `U(H)`: the smallest subring of `U(H)` containing
  `K[H]` that contains the inverse of each of its elements invertible in `U(H)`.
- `rk_G` is the Sylvester matrix rank function on `U(G)` given by the `N(G)`-dimension of the
  image. For `M in M_(m,n)(K[G])`, the kernel dimension of `r_M` on `l^2(G)^m` equals
  `m - rk_G(M)`. It is an integer iff `rk_G(M)` is.
- `rho_S` is the inner rank of a ring `S`: the least `r` such that `Y = PQ` with `P` of size
  `n x r` and `Q` of size `r x m`.

## Theorem (`atiyah-amalgam-rank-from-cohn-coproduct`)

Let `G = A *_C B`.

1. `D_C <= D_A` and `D_C <= D_B` as subrings of `U(G)`.
2. There is a unique ring homomorphism `phi: R := D_A *_(D_C) D_B -> U(G)` extending the
   inclusions of `D_A` and `D_B`, and a ring homomorphism `psi: K[G] -> R` such that
   `phi o psi` is the inclusion `K[G] <= U(G)`.
3. If `rk_G(phi(Y))` is an integer for every matrix `Y` over `R`, then `G` satisfies the Strong
   Atiyah conjecture over `K`.
4. For every matrix `Y` over `R`, `rk_G(phi(Y)) <= rho_R(Y)`. So if equality holds for every `Y`,
   then `G` satisfies Strong Atiyah over `K`. Conversely, every matrix `M` over `K[G]` with
   non-integral kernel dimension satisfies `rk_G(M) < rho_R(psi(M))`, and by the unmixed lemma
   its support meets both `A \ C` and `B \ C`.

No hypothesis on `C` is used. Property (T) enters only through the two dead frameworks.

## Proof

**(1).** Put `X = D_A cap U(C)`, a subring of `U(C)` containing `K[C]`. Let `x in X` be
invertible in `U(C)`, with inverse `y`. Since `U(C) <= U(A)` is a unital subring, `y` is also
the inverse of `x` in `U(A)`, and `D_A` is division closed in `U(A)`, so `y in D_A`. Hence
`y in X`, so `X` is division closed in `U(C)`, and minimality of `D_C` gives
`D_C <= X <= D_A`. The same argument gives `D_C <= D_B`.

**(2).** `R` is the coproduct of `D_A` and `D_B` over `D_C` in the category of rings. The
inclusions `D_A <= U(A) <= U(G)` and `D_B <= U(B) <= U(G)` agree on `D_C`, which gives `phi`.

`K[G]` is the coproduct `K[A] *_(K[C]) K[B]` of `K`-algebras. Given `K`-algebra maps
`f_A: K[A] -> S` and `f_B: K[B] -> S` agreeing on `K[C]`, they restrict to group homomorphisms
`A -> S^x` and `B -> S^x` agreeing on `C`. By the universal property of the amalgam these give
`G -> S^x`, which extends linearly to `K[G] -> S`. Uniqueness holds because `A cup B` generates
`G`.

The inclusions `K[A] <= D_A` and `K[B] <= D_B` agree on `K[C] <= D_C`, and so give `psi`. Both
`phi o psi` and the inclusion `K[G] <= U(G)` agree on `A cup B`. By uniqueness in the coproduct
property of `K[G]`, they are equal.

**(3).** `rk_G` is a Sylvester matrix rank function on `U(G)`, so `Y -> rk_G(phi(Y))` is one on
`R`. For `M` over `K[G]`, `rk_G(M) = rk_G(phi(psi(M)))`, which is an integer by hypothesis.

**(4).** Take `Y = PQ` with `P` of size `n x r`. Sylvester rank functions satisfy
`rk(PQ) <= rk(P) <= r`, so `rk_G(phi(Y)) <= rho_R(Y)`. Since `rho_R` is integer valued,
equality everywhere gives (3). For a non-integral `M`,
`rk_G(M) = rk_G(phi(psi(M))) <= rho_R(psi(M))`, and the inequality is strict because the right
side is an integer and the left side is not. The support statement is
`atiyah-amalgam-unmixed-matrices-reduce-to-factors`. QED

## Remarks (literature, not re-read from primary sources)

- **Linnell's criterion** (Linnell 1993; Lück, *L^2-Invariants*, Lemma 10.39): for torsion-free
  `H`, Strong Atiyah over `K` holds iff `D_H` is a skew field. With it, when `A`, `B`, `C` satisfy
  Strong Atiyah, `R` is a coproduct of skew fields over a skew field, and the converse of (3)
  also holds: Strong Atiyah for `G` puts `phi(R)` inside the skew field `D_G`, where all ranks
  are integers.
- **Cohn's coproduct theorem** (Cohn, *Free Ideal Rings and Localization in General Rings*): a
  coproduct of skew fields over a common skew subfield is a semifir with a universal field of
  fractions, whose rank function is `rho_R`. With it, the equality in (4) says that `D_G` is the
  universal field of fractions of `R`. The honest, maximal case is exactly what the Hughes-free
  theory produces when it applies.

These two remarks are context. The theorem above uses neither.

## What the reduction says about the open case

- **A counterexample** is a rank-deficient image of a Cohn-coproduct matrix, `phi*rk_G < rho_R`,
  with non-integer value, supported on both vertices.
- **A proof** can aim at the maximality statement `kazhdan-edge-coproduct-rank-is-inner-rank`.
  That is strictly stronger than needed (a non-universal epic `R`-field would still give integral
  ranks), but it is the natural uniform target. It is the statement the Hughes-free framework
  proves in the locally indicable case, and it makes no reference to amenability or indicability
  of `C`.

## Attempts recorded on the open claims

1. **Lück amenable-edge dimension flatness.** Dead at a (T) edge
   (`atiyah-kazhdan-edge-blocks-both-permanence-routes`).
2. **Hughes-free locally indicable division rings.** Dead: (T) forces finite abelianization, so
   `G` is not locally indicable. Same node.
3. **(T) controls only the trivial module.** Property (T) gives `b_1^(2)(C) = 0` (Bekka–Valette),
   i.e. `dim_(N(C)) Tor_1^(K[C])(N(C), K) = 0`. The Mayer–Vietoris computation over the
   Bass–Serre tree for a vertex-mixing matrix needs `dim Tor_1^(K[C])(N(C), M|_C)` for the module
   restricted from the vertex-mixing presentation, which (T) does not control.
4. **Approximation through finite-dimensional representations.** (T) makes the
   finite-dimensional representations of `C` isolated, but it produces no approximation of `G`.
   Lück-type approximation needs residual chains or sofic approximations of `G` itself, and none
   is known for the compression-host amalgams.
5. **Single-factor matrices.** On matrices over `K[A]`, `K[B]` or `K[C]`, `phi*rk_G` agrees with
   the factor ranks by the induction formula (unmixed lemma). So the inner-rank question is
   nontrivial only on alternating words in `D_A \ D_C` and `D_B \ D_C`.
