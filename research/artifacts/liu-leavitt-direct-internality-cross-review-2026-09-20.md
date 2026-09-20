# Independent review of the direct-internality Leavitt route

2026-09-20. **PASS as a conditional implication.** This is an independent
written audit of Sections 1--3 of
[the direct proof](liu-leavitt-direct-internality-and-consequences-2026-09-20.md)
and the route `leavitt-nonhyperlinear-from-internal-commutants`. It is not a
certification of Liu's upstream internality theorem or a formal verification.
No extra analytic hypothesis was needed in the steps reviewed below.

The analytic premise belongs to **Jihao Liu**,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7. The native Leavitt algebra and finite central-height
argument are the September 8 Cairn arguments. The separate all-fields
normalization application uses **Andreas Thom**,
[*A conditional construction of a nonhyperlinear group and the centralizer
problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf), Theorem 1.2,
or Liu's credited refinement, Theorem 1.3/7.4. The Leavitt deductions are
applications, not claims that either source states these conclusions.

## 1. Bounded slack is exactly enough for component selection

Let the full commutant of a canonical ICC Kazhdan model be
`C=[B_n]_omega`. Coordinate expectations onto `B_n` really induce `E_C`:
their output lies in C, and the difference is orthogonal to every bounded
coordinate sequence from `B_n`. Their uniform operator and L2 bounds
ensure that these operations descend to the quotient.

The property-(T) inequality on `L2(M)` therefore implies the stated
coordinate inequality with additive operator-unit-ball slack
`delta_n ->_omega 0`. A failure would give bounded coordinate witnesses
and contradict the inequality in the quotient. This conclusion is **not**
a coordinate inequality for all L2-unit vectors; no such upgrade occurs
later in the proof.

The same witness argument gives uniform almost commutation of each
generator lift with `U(B_n)`. Haar averaging into `B_n'` followed by polar
completion in that finite-dimensional algebra gives unitary corrected
lifts `W_(n,s)` at vanishing L2 distance. For contractions x, the change
in each squared commutator norm is bounded by `8 gamma_n`, since both
commutator norms are at most 2 and their difference is at most
`2 gamma_n`. Thus the stated slack `eta_n` is valid uniformly.

For `B_n=direct_sum_i M_(a_i) tensor I_(b_i)`, the weights are exactly
`lambda_i=a_i b_i/d_n`. Independent maximizing contractions `x_i` for
the component defects fit into the single ambient contraction
`direct_sum_i I_(a_i) tensor x_i`. Its expectation onto `B_n` is
`direct_sum_i tr_(b_i)(x_i) I_(a_i b_i)`. Both the variance and the
commutator terms split with those physical weights. Hence

```
sum_i lambda_i Delta_i <= eta_n.
```

Every `Delta_i` is nonnegative because zero is an admissible contraction.
This is essential: combining it with relation and trace errors cannot
hide a bad gap term by cancellation.

The ICC trace argument also uses these same weights. For M distinct
conjugates of g, the literal conjugate average has each component trace
equal to the trace of g. Its global squared L2 norm tends to `1/M`,
because distinct canonical group unitaries are orthogonal. Therefore
the weighted squared component traces tend to zero by letting M grow.
This does not require the corrected coordinate tuples to be exact
representations.

All relation words and all nonidentity group words are countable.
Slowly growing finite prefixes can be chosen along the fixed free
ultrafilter so that their total weighted error tends to zero. Selecting
a component of cost at most this mean simultaneously retains every
relation, the canonical trace, and `Delta_i ->_omega 0`.

Finally an arbitrary element of the full new commutant has a uniformly
operator-bounded representative. Scaling to contractions and applying
the selected bounded-slack inequality makes its distance to scalar
matrices tend to zero. The bounded scalar traces have an ultralimit,
so the element is one scalar in the ultraproduct. This checks the full
external commutant, not merely the commutant of the coordinate tuples.
No hidden strong Hilbert--Schmidt gap, heat scale, or dimension-growth
assumption is required.

## 2. Finite central height applies with the stated constants

For the native internal commutant `D=[A_n]_omega`, set
`E_n=E_(A_n)` and `F_n=Ad(U_n) E_n Ad(U_n*)`. The reversed subgroup
inclusion gives `D <= pi(u)Dpi(u)*`, hence `FE=E`. Uniformly bounded
contraction witnesses imply
`delta_n=||F_n E_n-E_n||_(infinity->2) ->_omega 0`.

The native unitary `y=uku^-1` lies in `pi(u)Dpi(u)*`, while its image
is a trace-zero element of the factor `pi(L)''`. For `z in D`, the
expectation of z onto that factor is central, hence scalar. Thus
`E_D(pi(y))=0`. The reverse map has a unitary norm-one witness; its
coordinate norm is also at most one because `I-E_n` is an L2
projection and `F_n` is contractive. Consequently
`rho_n=||E_n F_n-F_n||_(infinity->2) ->_omega 1`.

I independently checked the finite lemma's ingredients rather than
assuming an unquantified reversal principle. With central block weights
`w_i=tr(p_i)/a_i^2`, overlaps `m_ij=tr(p_i U p_j U*)` have identical
row and column marginals. Haar covariance and compression by central
supports give both `w_i H_ij <= m_ij` and `w_j H_ij <= m_ij` for the
Hilbert-space projection overlaps. These imply

```
up <= alpha_A <= delta^2,
down >= alpha_B-alpha_A >= rho^2/2-delta^2.
```

The last inequality follows from the Haar supremum-to-mean bound
`rho^2 <= 2 alpha_B`. Thus `down >= 1/4` on an omega-large set.
For the physical-weight median of `log(w_i)` and radius `1/16`,
the tail mass is at least `1/16`; one tail has mass at least `1/32`.
The appropriate monotone ramp has opposite constant level sets of
mass at least `1/2` and `1/32`, giving variance at least `1/64`.
Balanced flow converts its absolute increments to twice its upward
increments. The concavity bound for `1-exp(-r)` yields exactly

```
tr(z_n)=0, ||z_n||op<=1, ||z_n||_2>=1/8,
||[U_n,z_n]||_2^2 <= 2 delta_n^2/(1-exp(-1/16)).
```

There is no bounded-central-block-count or bounded-trace-distortion
assumption. Coordinate centrality puts z in `Z(D)`; it commutes with
u and with `pi(K) subset D`. The native identity
`H=<L,uKu^-1>` puts z in the global commutant, contrary to scalarity.

## 3. Scope of acceptance and the all-fields check

The first use of internality constructs the scalar-commutant model.
The second applies to its restriction to `L ~= H`, which is still a
canonical model of H after that isomorphism. Thus the restricted
canonical-model statement `(I_H)` in the proof is sufficient. The
route's universal `kazhdan-commutants-are-internal` premise supplies it.
The route also explicitly retains the elementary-group property-(T),
GL=EL and infinite-simplicity inputs. None is proved by this review.

I also checked the logical descent in
[the all-fields artifact](leavitt-all-fields-normalization-obstruction-2026-09-20.md).
Including coefficients of finite elementary factorizations of
`u,k_+,k_-` in the subring S ensures their membership in `EL_4(S)`;
it does not assume `GL_4(S)=EL_4(S)`. The displayed commutators generate
all missing elementary roots, and all-trace normalization kills the
nonidentity mark `x_24(a)`. The embedding into `R^x` uses the stated
four-leaf matrix-ring isomorphism. This descent needs no property-(T)
assertion for the entire unit group over an arbitrary field. Its
analytic premise is the stated normalization theorem, not the weaker
single-model internality hypothesis used in the F_2 direct proof.

**Acceptance:** the reviewed direct-internality conditional route is
valid with its displayed premises. The all-fields descent likewise
introduces no silent extra hypothesis. Neither acceptance promotes
the underlying analytic imports to proved status.
