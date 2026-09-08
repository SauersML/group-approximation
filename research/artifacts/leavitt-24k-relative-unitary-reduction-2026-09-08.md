# A 24k relative-unitary criterion for the binary Leavitt unit group

Date: 2026-09-08.  Source: an external note supplied by the user, which states
that it does not decide hyperlinearity of `H = L_(F_2)(1,2)^x` and instead
proves a direct matrix-feasibility reduction.  Everything below was re-derived
here before landing; no code was run and no Lean was built.

## 1. What is new relative to the archive

The archive already had a relative-unitary criterion:
`leavitt-regular-atlas-hyperlinearity-criterion` freezes two copies of `A_8`,
works in dimension `20160 k`, and routes through the universal central
extension `U_Q` with a fixed finite normal generating set.  The note's own
framing is correct: fixing finite subgroup representations is prior Cairn
material.  What is new here:

| | archive criterion | this one |
|---|---|---|
| frozen factors | `A_8 * A_8` | `C_3 * C_2^3` |
| base dimension | `20160 k` | `24 k` |
| passes through | universal central extension | nothing |
| relation data | a fixed finite normal generating set `bar_S` | a computable exhaustion `T_1 subset T_2 subset ...`, no finiteness asserted |

The factor in base dimension is `840`.  The price is that the relation family
is enumerable rather than finite -- the note explicitly declines to assert a
finite presentation, which is the honest trade.

Two inputs the note lists as assumptions are in fact established here and are
wired as prerequisites rather than hypotheses: the identification of the unit
group with `EL_3(R)` is `leavitt-gl-equals-el-and-perfect-unit-group`
(formalized, `GroupApproximation/KOne/AllRanksElementary.lean`), and
simplicity is `binary-leavitt-elementary-group-is-simple`.

## 2. The generating pair

With `v = s_0 t_1 + s_1 t_0` one computes `v^2 = 1`, `v s_0 = s_1`,
`t_0 v = t_1`, so `s_0, t_0, v` generate `R` as a unital ring.  Then
`c = (123)` and `b_1,b_2,b_3 = x_12(s_0), x_12(t_0), x_12(v)` generate
`EL_3(R)`, through

```text
[x_12(t_0), x_23(s_0)] = x_13(1),      [x_13(1), x_32(1)] = x_12(1),
```

after which cyclic conjugation and `[x_ij(a), x_jl(b)] = x_il(ab)` sweep every
coefficient.  `|B| = 8` is grading, not computation: the defining relations are
homogeneous for `deg s_i = 1`, `deg t_i = -1`, and `s_0, t_0, v` occupy degrees
`1, -1, 0`.

Landed as `binary-leavitt-units-generated-by-c3-and-c2-cubed`.  Note this is a
different four-element generating set from
`binary-leavitt-unit-group-four-generated`, whose four units are two per `A_8`
chart; the point here is that the four elements assemble into two finite
subgroups whose orders fix the model dimension.

## 3. The criterion and its separation half

Landed as `binary-leavitt-hyperlinear-iff-24k-feasible`.  The direction worth
naming is right-to-left, because that is where a criterion usually leaks: a
feasible sequence gives a homomorphism into a tracial matrix ultraproduct that
is nontrivial (`tr(C_k) = 0`, so `||C_k - I||_2 = sqrt 2`) and injective
(simplicity), and then finite models with the SAME separation constant `1` for
every finite subset are produced explicitly by `V -> (I (+) V)^(tensor r)`,
using `||V - I||_2^2 = 2 - 2 Re tr V` and `|(1+z)/2|^2 <= (1 + Re z)/2`.
So no separation requirement is quietly dropped.

The left-to-right direction is the rounding work: canonical traces by the same
amplification, eigenvalue rounding to cube roots and to signs (distance to the
nearest cube root is at most `|z^3 - 1|`), successive averaging to make three
involutions commute exactly (`||S_j - A||_2 <= ||I - A^2||_2` from
`1 - |a| <= 1 - a^2`), and character-projection counting to make both
multiplicities exactly regular after a 24-fold amplification.

## 4. The first relation, and why it is not an obstruction

`r_* = z c z c` with `z = a b a^(-1)` maps to `((12)c)^2 = 1`.  Telescoping
against `||C_k^2 - I||_2 = sqrt 2` gives the necessary bound

```text
||[pi(b_2), C_k pi(b_1) C_k^*] - I||_2 >= (sqrt 2 - ||pi(r_*) - I||_2)/2,
```

so a solution must keep the two frozen factors far from commuting -- `U = I`
fails.  But the same word evaluates to `1` exactly in `GL_3(F_8)` with
`b_1' = x_12(alpha)`, `b_2' = x_12(alpha^(-1))`, `b_3' = x_12(1)`, whose left
regular representation restricts to regular multiples on both finite
subgroups; `|GL_3(F_8)| = 115379712 = 24 * 4807488`.  So the first relation has
an exact model and cannot yield nonhyperlinearity.  That assignment is not a
ring map from `R` -- `(LG2)` would force `s_1 = s_0`, `t_1 = t_0`, against
`t_0 s_1 = 0`.

Landed as `leavitt-24k-first-relation-has-exact-finite-model`.  This is the
node that stops the attractive misreading of the commutator bound.

## 5. What the supplied MF obstruction gives, and what it does not

Both recorded in the attempts of the two branch claims.  For each fixed `k`,
compactness plus the MF-homomorphism obstruction forces some `m(k)` with a
strictly positive minimum, so a successful family must leave every finite set
of dimensions.  In OPERATOR norm a uniform gap already follows from the same
obstruction (`||C_k - I||_op = sqrt 3`).  Neither gives the normalized-HS
statement: `diag(-1,1,...,1)` is at operator distance `2` and HS distance
`2/sqrt d`.

## 6. Status

The reduction is landed; the matrix problem is not solved.  The two branches
are `leavitt-24k-feasibility-vanishes` (route to
`binary-leavitt-unit-group-hyperlinear`, and thence to a hyperlinear nonsofic
group) and `leavitt-24k-feasibility-has-a-uniform-gap` (route to
`non-hyperlinear-group`, the program goal).  Exactly one holds; the archive now
carries both as explicit finite-dimensional optimization statements over one
`24k`-dimensional unknown.
