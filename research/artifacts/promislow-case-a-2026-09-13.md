# Case A of Higman's unit conjecture for the Promislow group (lane hl-promislow-case-a, 2026-09-13)

**Target.** `integral-unit-conjecture-torsion-free` on `P`, which is equivalent
on `P` to `rational-unit-conjecture-torsion-free` by
`rational-units-rescale-to-integral-units`. The route
`integral-unit-conjecture-from-rational-proof` goes rational ⇒ integral.

The starting point is 56b86b07d, `promislow-integral-units-have-monomial-definite-line-shadows`.
Every unit of `Z[P]` is a signed monomial modulo each of
`I_A = (y+1, z+1)`, `I_B = (x+1, z+1)` and `I_C = (x+1, y+1)`. Units trivial
modulo 2 (Case A) lie in `epsilon + (I_A cap I_B cap I_C)`.

**Verdict: partial.** No unit was found and no triviality was proved. Three new
claims landed:

1. `promislow-shadow-kernel-intersection-is-line-vanishing`: the intersection is
   explicit, `I_A cap I_B cap I_C = sum_c (XY, XZ, YZ) c` with `X = x+1`, etc.
2. `promislow-unit-conjecture-from-shadow-monomial-fp-units`: a
   characteristic-`p` criterion for Higman's conjecture on `P`, plus what a
   counterexample produces in every large characteristic.
3. `promislow-fp-has-nontrivial-shadow-monomial-units`: that criterion's
   hypothesis fails at `p = 2, 3, 5, 7`.

## Step 1 of the directive: filtration by the augmentation-type ideal

The directive proposed filtering `Z[P]` by powers of
`J = (x+1, y+1, z+1)`, and arguing that invertibility forces the leading term of
`u - epsilon` to vanish.

**Dead as stated.**
- **What the graded ring looks like.** `gr_J Z[P]` is a twisted polynomial ring
  `H[X, Y, Z]` over the Lipschitz order `H = Z<i, j>`, where `i` and `j` fix one
  of `X, Y, Z` and negate the other two. It is a domain.
- **Why leading terms decide nothing.** In the `J`-adic completion every element
  of `1 + J` is invertible, so the leading-term map cannot separate units from
  non-units. Over `Z[P]` itself, units `1 + w` with `w in J^n` satisfy
  `w' = -w mod J^(2n)` for the inverse `1 + w'`, which is consistent in every
  degree.
- **Agreement with known results.** Bartholdi's approximate units modulo every
  `n` (Tabei, Remark 3.3, as recorded on `integral-unit-conjecture-torsion-free`)
  say the same: no congruence information closes Case A.

A proof has to use global integrality, e.g. positivity as the definite shadows
do, not a filtration.

## Step 2 of the directive: further positive-definite quotients

The directive asked for further quotients with a sum-of-squares norm. None were
found beyond the three lines. What follows is the analysis, not a landed claim.

- **Degree-2 fibres.** `Q[P]` is a crossed product of `Q(L)` by `K4`, of degree 4
  over `Q(L)^(K4)`. At a character `chi` of `L` the fibre algebra has degree 2 or 1
  only if some nontrivial element of `K4` fixes `chi`. So two of `x, y, z` go to
  `+-1`: the lines of `K4`-fixed characters.
- **Which lines are definite.** On the line where `y, z -> (y_0, z_0)` with
  `x` free, the relator forces `z_0 = y_0` for the untwisted commutation. The norm
  form is `l_0 l_0bar - y_0 l_1 l_1bar`, definite only for `y_0 = -1`. That is the
  existing shadow A.
  - With `z_0 = -y_0`, the commutation becomes `u t = -t^-1 u`. The constant term
    of `l(t) l(-t^-1)` is `sum (-1)^m l_m^2`, which is indefinite.
  - The same holds on the other two lines.
- **The fixed point.** `(x, y, z) = (-1, -1, -1)` gives the Hamilton order
  `Z<i, j>`. It is a specialization of all three shadows.
- **Number-field specializations.** Specializing the line parameter `t` to a
  number (a root of unity for positivity) gives orders in definite quaternion
  algebras over totally real fields. Their unit groups contain non-monomial units
  (e.g. Hurwitz units), so these specializations are weaker than the lines
  themselves.
- **Generic fibres.** They have degree 4. Over `R` they are `M_4(R)` or
  `M_2(H)`, and orders there have infinite unit groups with no monomiality
  constraint.

**Conclusion.** The three definite lines are the complete supply of this kind of
positivity input, and Case A is exactly what they leave out.

## Where Case A units live

`promislow-shadow-kernel-intersection-is-line-vanishing`: a Case A unit is
`epsilon + p + q a + r b + s ab`. Each of `p, q, r, s` lies in `(XY, XZ, YZ) Z[L]`,
the ideal of the union of the three coordinate lines through `(-1,-1,-1)`.

## Characteristic p: the criterion and its failure at small primes

**The criterion.** `promislow-unit-conjecture-from-shadow-monomial-fp-units`.
Integral units reduce, for every `p`, to units of `F_p[P]` with monomial shadows.
If such units are trivial for infinitely many `p`, every integral unit is trivial;
large primes read the integer coefficients back.

**The failure.** `promislow-fp-has-nontrivial-shadow-monomial-units`.

- **`p = 2`.** Twist Gardam's unit `u` by the diagonal automorphisms `sigma_h` of
  the affine model (conjugation by `diag(+-1, +-1, +-1)`).
  - `u sigma_h(u)^-1` is a nontrivial unit for all seven `h`, with supports 61 to
    165.
  - For `h = (1,1,-1), (-1,1,1), (-1,1,-1)` all three shadows are monomials.
  - For the other four, shadow B is not.
- **`p = 3, 5, 7`.** Murray's units have a monomial shadow on line C, and `z`
  maps to `t^2` on C and to `-1` on A and B.
  - So every commutator `[u, z]` has monomial shadows, and it is nontrivial for
    all 8 parameter pairs at each prime.
  - Also 384 of the 4032 ordered quotients among twisted Murray units have
    monomial shadows.
  - In the earlier twist-only run, none of the 168 twists `u sigma_h(u)^-1` has all
    three shadows monomial. Shadow C is always monomial there, while A or B fails.

**Scripts and logs** (MSI, Python 3.12; md5 in the route):
- `promislow-shadow-twisted-units.py`, log `promislow-shadow-twisted-units-run-2026-09-13.log`;
- `promislow-shadow-twisted-units-odd.py`, log `promislow-shadow-twisted-units-odd-run-2026-09-13.log`.

## Exact gap

- **(G1) Characteristic-zero structure.** Any proof of Case A must use
  information in characteristic 0 beyond the three definite shadows. At
  `p = 2, 3, 5, 7` there are nontrivial units that agree with trivial units on all
  three shadows. Candidates:
  - archimedean positivity on non-definite fibres, where the involution trace
    `tau(v v*) = ||v||^2` is positive but not forced to 1;
  - a height / Mahler-measure argument on the quartic reduced norm, where
    `Nrd(v) = +-1` carries no Mahler information;
  - integrality in unbounded degree.
- **(G2) Counterexamples in large characteristic.** A counterexample `v` gives,
  for every prime `p > 2|v|`, a nontrivial shadow-monomial unit of `F_p[P]`
  supported on `supp(v)`. The commutator mechanism supplies such units at every
  small prime, but with supports that depend on `p`: Murray's supports grow with
  `p`. So the open question is whether one fixed finite support carries
  shadow-monomial units at all large primes.
