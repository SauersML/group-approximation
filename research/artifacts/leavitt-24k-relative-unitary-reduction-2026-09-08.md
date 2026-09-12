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

Here is the precise finite exhaustion used by the criterion. Work in the
free polynomial algebra `F_2<s_0,s_1,t_0,t_1>` with the five defining
polynomials `t_i s_j-delta_(ij)` and `s_0 t_0+s_1 t_1-1`.
For `m>=1`, let `E_m` contain every reduced word in `C_3*C_2^3` of
free-product syllable length at most `m` for which all nine entries of
its expanded matrix minus `I` admit certificates

```text
entry=sum_(nu=1)^q a_nu p_(i_nu) b_nu,
q<=m,     length(a_nu)<=m,     length(b_nu)<=m,
```

where the `p_i` are the five polynomials and the factors `a_nu,b_nu`
are monomials. The empty sum certifies zero. Define

```text
T_m={r_*} union E_m,
```

with the fixed kernel word `r_*` of Section 4. For clarity, its full
definition is

```text
d=[b_2,c b_1 c^(-1)],       a=[d,c^2 d c^(-2)],
b=c d c^(-1),              z=a b a^(-1),
r_*=z c z c.
```

The elementary-root calculation gives `q(d)=x_13(1)`,
`q(a)=x_12(1)`, `q(b)=x_21(1)`, and `q(z)=(12)`; hence
`q(r_*)=((12)c)^2=1`. In particular `r_*` belongs to every `T_m`
by the explicit adjoin convention, independently of its certificate length.

Both the bounded words and the bounded certificates range over finite
computable sets. Free polynomial equality is decidable by collecting
monomials, so each `T_m` is a computable finite set. They are nested,
and their union is the whole kernel: any fixed kernel word has finite
length and finite ideal certificates for its nine entries. This uses
no finite-presentation assertion for the unit group.

The word-length condition corrects a material omission in the earlier
certificate-only definition. Put `u=b_1 c b_1 c^(-1)`. Its powers
are distinct reduced words in the free product, whereas

```text
q_free(u)=x_12(s_0)x_23(s_0),       q_free(u)^4=I
```

already over the free characteristic-two polynomial algebra. Indeed
`q_free(u)=I+M` with `M` strictly upper triangular, so `M^3=0`
and `(I+M)^4=I`. Every `u^(4j)` consequently has zero certificates
in all nine entries. A certificate bound alone therefore includes
infinitely many words at each stage. The reduced word-length bound
removes that defect while preserving the exhaustive criterion.

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

## 7. Scalar phases can be removed by tensoring with the conjugate tuple

There is an equivalent version of the same criterion in which every selected
relator need only approach a scalar unitary. This is a direct matrix
consequence of the established criterion, not a construction of feasible
tuples or a decision of hyperlinearity.

Write `P=C_3*C_2^3`, and on the basis `|a,b,j>` of
`C^3 tensor C^8 tensor C^k` use the frozen representations

```text
C_k |a,b,j> = |a+1,b,j>,
D_(i,k) |a,b,j> = |a,b+e_i,j>,
pi_(k,U)(c)=C_k,       pi_(k,U)(b_i)=U D_(i,k) U^*.
```

Here `a` is read modulo three and `b` lies in `F_2^3`. Each `pi_(k,U)` is
an exact representation of the free product. For the finite relation sets
`T_m` from Section 3, define

```text
Delta_m = inf_(k>=1, U in U(24k)) max_(r in T_m)
              ||pi_(k,U)(r)-I||_2,

Delta_m^sc = inf_(k>=1, U in U(24k)) max_(r in T_m)
              min_(|zeta|=1) ||pi_(k,U)(r)-zeta I||_2.
```

All norms and traces below are normalized in the displayed matrix dimension.
Then, for every `m`,

```text
Delta_m^sc <= Delta_m <= sqrt(2) Delta_m^sc.              (SP1)
```

Consequently

```text
H is hyperlinear  <=>  Delta_m^sc=0 for every m.         (SP2)
```

**The exact norm identity.** For a unitary `V` in `M_d(C)`, write
`z=tr_d(V)` and let `bar V` mean entrywise complex conjugation. Minimizing
over the scalar phase gives

```text
min_(|zeta|=1) ||V-zeta I||_(2,d)^2 = 2-2|z|.
```

Since the normalized trace of `V tensor bar V` is `|z|^2`,

```text
||V tensor bar V-I||_(2,d^2)^2
  = 2-2|z|^2
  = (1+|z|) min_(|zeta|=1) ||V-zeta I||_(2,d)^2.         (SP3)
```

In particular the norm increases by at most `sqrt(2)` relative to the best
scalar defect. Formula `(SP3)` also covers zero defect: an exact scalar
unitary becomes the identity.

**Restoring the frozen finite factors.** Given a tuple `pi=pi_(k,U)` in
dimension `d=24k`, form the exact free-product representation

```text
rho(g)=pi(g) tensor bar(pi(g)).
```

Entrywise conjugation preserves multiplication, so the same formula holds
for every evaluated word, including inverses. Its dimension is

```text
d^2=(24k)^2=24K,             K=24k^2.                    (SP4)
```

For either finite factor `F=C_3` or `C_2^3`, the restriction of `pi` is a
multiple of the regular representation. Thus its normalized character is
one at the identity and zero elsewhere. The normalized character of
`rho|_F` is the squared modulus of that character, hence is again the regular
character. Finite-group character theory therefore makes `rho|_F` exactly
a regular multiple, of multiplicity `d^2/|F|`.

Choose one global unitary conjugation taking `rho(c)` to `C_K`. After this
conjugation the second factor is still an exact regular multiple; matching
its simultaneous character eigenspaces with those of the frozen `D_(i,K)`
gives a unitary `U'` such that all three generators are
`U' D_(i,K) U'^*`. The conjugated tuple is therefore exactly
`pi_(K,U')`. Word defects are unchanged by this global conjugation.

Applying `(SP3)` to every `pi(r)`, `r in T_m`, now gives

```text
max_(r in T_m) ||pi_(K,U')(r)-I||_2
  <= sqrt(2) max_(r in T_m) min_(|zeta|=1)
                                     ||pi_(k,U)(r)-zeta I||_2.
```

Taking infima proves the second inequality in `(SP1)`; the first follows
by allowing the phase `zeta=1`. Section 3 then proves `(SP2)`. In particular,
the original trace-zero generator stays trace zero after tensoring, so this
operation retains the nontriviality used in the separation argument.

**Scope of the phase freedom.** The minimizing phases may be chosen
independently for different relators and different stages. No cocycle
compatibility condition is required: the single representation
`pi tensor bar pi` cancels every scalar phase at once. The hypothesis is
proximity to scalar matrices on the whole space, however, not proximity to
the center of a proper matrix subalgebra. For example,
`V=diag(I_l,-I_l)` is central in `M_l(C) direct-sum M_l(C)`, but
`tr(V)=0` and `||V tensor bar V-I||_2=sqrt(2)`. Merely central relators
therefore do not satisfy the needed scalar condition.

This section is a written matrix argument only; no code or Lean was run.

### 7.1. Arbitrary scalar phases on common permutation coordinates do not suffice

The scalar freedom in `(SP2)` does not make a permutation construction viable.
Using the established simplicity, perfectness, and nonsoficity of `H`, every
homomorphism from `H` into a normalized-HS metric ultraproduct of monomial
unitary groups is trivial. In particular, a sequence of regular-factor
tuples whose defects tend to zero on every `T_m` cannot be jointly monomial
in one common basis at each stage; neither can full canonical microstates.
That basis may vary with the stage, and all nonzero matrix entries may have
arbitrary phases in the unit circle.

Here is the metric argument. In a fixed basis write a monomial unitary as
`U=D P_sigma`, with `D` diagonal unitary, and let `p(U)=sigma`. The map `p`
is a group homomorphism. If the permutations underlying two monomial
unitaries differ on a basis vector, their images of that vector are
orthogonal. Summing these column contributions gives

```text
d_H(p(U),p(V)) <= (1/2) ||U-V||_2^2.                    (SP5)
```

Consequently projection to the permutations is well defined on metric
ultraproducts. Given a homomorphism `rho` from `H` to the monomial
ultraproduct, its permutation projection has kernel either all of `H` or
the identity, by simplicity. The latter case would make `H` sofic. To see
that no uniform separation assumption is missing, an injective permutation
ultraproduct map gives each nonidentity element a positive limiting Hamming
distance from the identity. On a finite set, take a common positive lower
bound and pass to the diagonal action on a fixed Cartesian power: a moved
fraction `h` becomes `1-(1-h)^r`, while multiplication errors increase by
at most `r`. This produces the usual sofic separation on that finite set.
Nonsoficity therefore forces the permutation projection of `rho` to be
trivial.

The kernel left after that projection is abelian. Indeed, for each
monomial representative `U=D P_sigma`,

```text
||U-D||_2^2 = ||P_sigma-I||_2^2 = 2 d_H(sigma,I).       (SP6)
```

If the permutation class is trivial, `(SP6)` replaces `U` by a diagonal
unitary without changing its HS ultraproduct class. All these diagonal
classes commute. Thus `rho(H)` is abelian, and perfectness of `H` forces
`rho` itself to be trivial. A regular-factor tuple contradicts this because
its generator `c` has trace zero and distance `sqrt(2)` from the identity.

The same exclusion holds if the images of a fixed finite generating set
are asymptotically close to monomial unitaries in one common basis per
stage. Choose such monomial approximants for the generators. Telescoping
changes every fixed word by a vanishing HS error, so the approximants
retain the relations and the trace-zero separator in the ultraproduct.
They would give precisely the forbidden nontrivial monomial homomorphism.

Finally, this also excludes monomial or asymptotically monomial tuples
whose relators only become scalar as in `(SP2)`. Tensoring with the entrywise
conjugate tuple preserves monomiality in the tensor-product basis and, by
`(SP3)`, makes those relators approach the identity. If the original
generators are merely close to monomial matrices, the tensor products remain
close, since
`||U tensor bar U-V tensor bar V||_2 <= 2||U-V||_2`.
The preceding contradiction then applies. Individual diagonalizability
of each generator supplies no such restriction: the common basis for the
whole tuple is essential.

The archive's signed-monomial and uniformly discrete finite-label criteria
use additional restrictions on the phases or labels. The argument here
permits arbitrary circle phases and uses the specific group properties of
`H`; it does not assert that arbitrary monomial HS images of other groups
are sofic. This rules out the stated construction class, not arbitrary
unitary models of `H`.
