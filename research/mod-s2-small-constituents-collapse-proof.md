---
rg: 2
id: mod-s2-small-constituents-collapse-proof
kind: route
title: Put the determinant line of an admissible constituent into a longer tensor word, read the tensor-word loss off it, and feed the Torelli-abelian approximant of the dichotomy into the census bound
target: mod-s2-small-constituents-collapse-to-torelli-abelian-reduction
requires:
  - mod-s2-near-scalar-torelli-closure-dichotomy
  - mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
  - mod-s2-jones-torelli-closure-is-su5
---

Notation as in the target. From `mod-s2-near-scalar-torelli-closure-dichotomy` the proof uses (CD2), (CD3)
and the facts listed at the start of its proof: `S` is normal in `G = cl rho(M)`, and all these groups are
compact. From `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit` it uses (TA1). From
`mod-s2-jones-torelli-closure-is-su5` it uses (JC1) and (JC2).

## Step 1: `D(rho) <=` weight of every admissible `W` (C1, lower bound)

Let `W <= V_ab` be an irreducible `H`-subrepresentation, `n = dim W`, with `3 not| (a - b) n`.
- `Lambda^n W` is a line inside `W^(x n)`, which lies in `V_ab^(x n)`.
- `V_ab^(x n)` is isomorphic to `V_(na, nb)` as a representation of `U(d)`, hence of `G` and of `H`. The
  isomorphism is the unitary that reorders the tensor factors, and it commutes with `u^(x a) (x) conj(u)^(x b)`
  factorwise.
- `h in H` acts on `Lambda^n W` by `det(h|_W)`. This is a continuous character of `H`, so it is trivial on
  commutators and hence on `S = cl[H, H]`.

So `V_(na, nb)^S != 0`. Since `na - nb = (a - b) n` is prime to 3, the definition of `D` gives
`D(rho) <= n(a + b)`.

## Step 2: the minimum is attained (C1, upper bound)

If `D(rho) = infinity`, Step 1 shows no admissible `W` exists, and both sides of (C1) are infinite.
Otherwise take `(a, b)` with `a + b = D(rho)`, `3 not| a - b` and `V_ab^S != 0`.
- `V_ab^S` is `H`-invariant because `S` is normal in `H`.
- `H` acts on it through the compact abelian group `H/S`, so it splits into `H`-invariant lines.
- Any such line `W` is irreducible and admissible (`dim W = 1`), and has weight `a + b = D(rho)`.

With Step 1 this proves the identity. By (CD2), `D(rho) = infinity` iff case (a) holds.

## Step 3: the bound in (C1)

Let `W` be admissible. By Steps 1 and 2 we are outside case (a), and `D = D(rho) <= (a + b) dim W`. Take
`(a', b')` attaining `D`.
- (CD3) gives an honest Torelli-abelian `sigma` with `||sigma(t_s) - omega^(+-1) I|| <= D eps`.
- (TA1) gives `min_(+-) ||sigma(t_s) - omega^(+-1) I|| >= 2 sin(pi d_inf)`, and by definition this is
  also `c_ab`.

So `(a + b) dim W * eps >= D eps >= c_ab`. For the comparison with (PC2): `sin` is concave on `[0, pi]`, so
`sin(x/n) >= sin(x)/n`, and hence (PC2) is the stronger bound on the row `(1, 0)`.

## Step 4: (C2)

- **(i) implies (ii).** The row `a = 1, b = 0` consists of the irreducible `H`-subrepresentations of `C^d`,
  which are the Torelli constituents. On that row, admissible means `3 not| dim W` and the weight is
  `dim W`. So the set of quantities in (SB_tw) contains the set in (SB), and its infimum is at most the
  infimum in (SB). If the latter is 0, so is the former.
- **(ii) implies (iii).** Suppose `1/3 in Z_hon`. By (ii) there are honest `rho_j` and admissible `W_j` with
  `(a_j + b_j) dim W_j * arcsin(eps_j/2) -> 0`. Since `eps = 2 sin(arcsin(eps/2)) <= 2 arcsin(eps/2)`,
  the products `(a_j + b_j) dim W_j * eps_j` also tend to 0. By Step 3 each is at least `c_ab`, so
  `c_ab = 0`. By (CD5) of the dichotomy, which restates the definition of `Z_ab`, this means
  `1/3 in Z_ab`.
- **(iii) implies (i).** Suppose `1/3 in Z_hon`. By (iii) there are honest Torelli-abelian `sigma_j` with
  `||sigma_j(t_s) - omega I|| = eps_j -> 0`. Since `sigma_j(K)` is abelian, every Torelli constituent of
  `sigma_j` has dimension `1`, which is prime to three. So the infimum in (SB) is at most
  `arcsin(eps_j/2) -> 0`.

So (i) implies (ii), (ii) implies (iii), and (iii) implies (i). The statement about (PC5) follows because
(TAP) is `d_inf > 0`. By (TA1), `c_ab = 2 sin(pi d_inf)` with `0 <= d_inf <= 1/3`, so (TAP) is
`c_ab > 0`, which is `1/3 notin Z_ab`. The gap is
`1/3 notin Z_hon`, since `Z_hon` is closed under negation, as used in the proof of (PC5). So "(TAP) and (SB)"
reads "`1/3 notin Z_ab` and (`1/3 in Z_hon` implies `1/3 in Z_ab`)", and that is equivalent to
`1/3 notin Z_hon`.

## Step 5: (C3)

Take `x` with `0 < |x| < pi/8` and `x/pi` irrational. By (JC1), `H = S = SU(V, B)`, which contains
`zeta I` since `det(zeta I_5) = zeta^5 = 1`. Let `W <= V_ab` be an irreducible `H`-subrepresentation,
`n = dim W`, with `5 not| a - b`.
- The central element `zeta I` acts on `V_ab`, hence on `W`, by `zeta^(a - b)`.
- `det(zeta I |_W) = zeta^((a - b) n)`.
- As in Step 1, `det(. |_W)` is a character of `H` trivial on `S = H`, so it is trivial at `zeta I`.

So `5 | (a - b) n`, hence `5 | n`. The statement `eps_zeta -> 0` as `x -> 0`, and the witness `chi_zeta`, are
(JC2) as quoted. QED.
