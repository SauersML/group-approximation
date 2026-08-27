# Moment-exact qutrit splice, fixed-space no-go, and rank-router handoff

Date: 2026-08-23

## Scope

This note integrates a groupification reduction extracted from Culf--Mastel,
*RE-completeness of entangled constraint satisfaction problems*
(arXiv:2410.21223v2).  It does not claim a finished nonhyperlinear group.
It records the exact part that is now proved, the tensor-closure obstruction
to the first direct gadget, and the resulting handoff to the shared hybrid
rank router.

The rank-router route
first converts a source game to an independent-set game and asks a role
packet to authenticate

```text
diag(A,B)  and  diag(AB,1).
```

The route here instead converts positive ONE3 clauses to order-three clocks
exactly and reduces consistency to equality of one spectral projection.
The most permissive direct fixed-projector synchronizer is tensor-closure
inconsistent.  The five-edge diamond therefore supplies a second semantic
front end to the same rank router rather than a second open group endpoint.

## 1. Pointed weighted defect gaps

For a weighted star algebra `(A,mu)`, a word or polynomial `w in A`, and
`delta>0`, define

```text
gamma_(A,w)(delta)
  = inf { def_A(tau) : tau tracial, ||w-1||_tau^2 >= delta }.
```

If `alpha:(A,mu)->(B,nu)` is a `C`-homomorphism and `alpha(w)=v`, then

```text
gamma_(B,v)(delta) >= C^(-1) gamma_(A,w)(delta).        (PMG1)
```

Indeed, for every trace `rho` in the infimum on the left,
`tau=rho o alpha` has the same pointed moment and

```text
def_A(tau) <= C def_B(rho).
```

This elementary observation makes a chosen nontrivial moment compatible
with the weighted-defect calculus rather than merely with exact
satisfiability.

## 2. Culf--Mastel Lemma 3.10 is moment-exact on global variables

In the proof of Lemma 3.10, start from a trace

```text
tau = rho o phi
```

on the assignment algebra with commutation defect.  The construction rounds
and rebuilds the context measurements, but for every global assignment
variable `x` it sets

```text
chi(sigma'(x)) = phi(x).                                (PMG2)
```

Consequently, for every noncommutative star polynomial `p` in the global
assignment variables,

```text
tau'(p) = tau(p),                                      (PMG3)
```

while

```text
def(tau') <= poly(k^L) def(tau).                        (PMG4)
```

The new operators are constructed inside the same tracial von Neumann
algebra.  Therefore a Connes-embeddable input trace yields a
Connes-embeddable output trace.  In combination with `(PMG1)`, the
trace-dependent rounding transports pointed defect gaps for every witness
living in the global assignment algebra.

Applied to the fixed tracial/non-CE BCS and the paper's Boolean
fixed-language reductions, this yields a finite positive-ONE3 weighted BCS
which has a tracial perfect model, has no CE perfect model, and retains every
chosen global-variable moment exactly.  The associated finite-dimensional
defect floor is still positive, with constants depending only on the fixed
instance.

## 3. Positive ONE3 is exactly one qutrit clock

Let `omega=exp(2 pi i/3)`.  Hidden values

```text
h_y=h_x-1,             h_z=h_x+1       in Z_3          (Q13-1)
```

have precisely the solutions

```text
(0,2,1), (1,0,2), (2,1,0).
```

Decoding `b_i=1` iff `h_i=0` gives exactly

```text
100, 010, 001.                                          (Q13-2)
```

Operator-algebraically, let `T^3=1`, let `E_a=Pi_a(T)` be the spectral
projection for eigenvalue `omega^a`, and put

```text
U_x=T,       U_y=omega^(-1)T,       U_z=omega T.
```

Then

```text
Pi_0(U_x)=E_0,   Pi_0(U_y)=E_1,   Pi_0(U_z)=E_2,
E_0+E_1+E_2=1.                                         (Q13-3)
```

Thus the local ONE3 context algebra `C^3` is exactly `C[Z_3]`.  With a
central order-three letter `J` represented by `omega`, the clause uses only
ordinary group-style equations

```text
U_y=J^(-1)U_x,           U_z=J U_x.                    (Q13-4)
```

If one Boolean variable occurs in position `a` of clause `c` and position
`b` of clause `d`, the only remaining consistency relation is

```text
Pi_0(J^(-a)T_c) = Pi_0(J^(-b)T_d).                     (Q13-5)
```

Every local nonlinear clause has disappeared.  The full compiler has been
reduced to synchronizing the fixed-space projection of two order-three
elements while leaving their other two spectral subspaces free.

## 4. Two exact no-go theorems

### 4.1 Literal group-algebra equality is too strong

For order-three group elements `u,v`,

```text
Pi_0(u)=(1+u+u^2)/3.
```

Linear independence of the group basis gives

```text
Pi_0(u)=Pi_0(v)  =>  {u,u^2}={v,v^2}
                   =>  v=u or v=u^(-1).                (NO1)
```

After cutting by a fixed central character, the basis is indexed by cosets
of the central subgroup.  The same argument aligns the cyclic subgroup up
to central phase and inversion.  Hence a literal identity in a group
algebra synchronizes the entire clock, not just its fixed space.

### 4.2 Commuting scalar gadgets remain affine

For commuting order-`p` interface and auxiliary elements, every ordinary
word equation becomes one affine equation over `F_p` on scalar characters.
The solution set is affine, and projection along existential auxiliaries is
again affine.  Positive one-hot support over `F_2` and qutrit inequality over
`F_3` are not affine.  Therefore no entirely commuting finite-phase scalar
gadget can supply the missing selector/synchronizer relation.

Together `(NO1)` and the affine-shadow theorem show that the remaining
gadget must use a genuinely tracial/dimensional identity.  It cannot be a
disguised exact subgroup relation or an existential affine pp definition.

## 5. A five-edge diamond already gives the analytic synchronizer

For a 3-colouring triangle `(x,a,b)`, put

```text
D(x,a,b)
  = sum_c ( ||P_c(x)P_c(a)||_2^2
           +||P_c(x)P_c(b)||_2^2
           +||P_c(a)P_c(b)||_2^2 ).
```

Culf--Mastel Lemma 8.3 gives

```text
sum_c ||P_c(x)+P_c(a)+P_c(b)-1||_2^2 = 2D(x,a,b).      (DIA1)
```

For the diamond formed by `(x,a,b)` and `(y,a,b)`, subtract the two
triangle residuals and use the squared triangle inequality:

```text
sum_c ||P_c(x)-P_c(y)||_2^2
 <= 4(D(x,a,b)+D(y,a,b)).                              (DIA2)
```

Thus five same-colour overlap edges robustly synchronize the entire qutrit
PVM with linear defect.  Analytic PVM synchronization is not the open
problem.  The open problem is to charge the five overlap energies by
ordinary group-word defects without converting `(Q13-5)` into the literal
subgroup equality forbidden by `(NO1)`.

The hybrid rank router can in principle wordize each overlap term in
`(DIA2)`, subject to its separate authenticated two-copy block assembler.
The apparently smaller direct fixed-space gadget considered below is not an
independent viable endpoint: tensor closure refutes its completeness and
soundness requirements simultaneously.

## 6. The proposed direct endpoint: PSync_3

Seek a finite ordinary-group gadget with:

- a central element `J` with `J^3=1`;
- order-three interface elements `u,v`;
- a fixed finite relator list `r_1,...,r_m`; and
- a constant `K`;

such that every tracial representation in the sector `J=omega` satisfies

```text
||Pi_0(u)-Pi_0(v)||_2^2
  <= K sum_j ||r_j-1||_2^2.                             (PS3-1)
```

Perfect completeness must retain complement freedom: whenever two
order-three unitaries `U,V` satisfy `Pi_0(U)=Pi_0(V)`, the pair extends,
after one fixed amplification if necessary, to a zero-defect representation
of the gadget, without requiring `U=V` or `U=V^(-1)`.  The extension should
remain inside the amplified original tracial algebra, hence preserve CE when
the input algebra is CE.

The natural certificate-search formulation would be a cyclic sum-of-squares
inequality for `(PS3-1)`.  The certificate would have to be tracial rather
than a literal identity in the central-character group algebra.  Section 8
shows that even arbitrary noncommuting auxiliaries cannot meet these two
requirements.

## 7. The formerly conditional terminal bridge

Assume PSync_3.  Start with the finite positive-ONE3 weighted system obtained
from the fixed tracial/non-CE BCS.  Introduce one clock `T_c` for each clause,
use `(Q13-4)` for the three local positions, and attach a copy of PSync_3 for
every repeated-variable consistency equation `(Q13-5)`.

The perfect tracial ONE3 model extends to an exact tracial representation
with `J=omega`.  Conversely, any CE trace of the resulting group in the
`J=omega` sector satisfies every PSync estimate with zero right-hand side.
Equations `(Q13-3)--(Q13-5)` therefore decode a perfect CE trace of the
positive-ONE3 system, contradicting its no-CE property.

Finally, an exact representation with `J=omega` proves that `J` has order
three.  If the group were hyperlinear, its canonical group factor would be
CE.  The central projection

```text
e_omega=(1+omega^2 J+omega J^2)/3
```

has canonical trace `1/3`; normalizing the canonical trace on this corner
would give a CE trace in the forbidden `J=omega` sector.  Hence the group is
nonhyperlinear.

The complete direct cascade is therefore

```text
tracial/non-CE BCS
 -> moment-exact positive ONE3 weighted system
 -> one qutrit clock per clause
 -> PSync_3 on repeated-variable incidences
 -> no CE omega-sector
 -> nonhyperlinear group.
```

This cascade is useful for locating the desired interface, but it is not a
viable terminal because PSync_3 is refuted below.

## 8. Tensor closure refutes complement-flexible PSync_3

Complement-flexible completeness applies to the four scalar pairs

```text
(U_1,V_1)=(omega,   omega),
(U_2,V_2)=(omega,   omega),
(U_3,V_3)=(omega^2, omega),
(U_4,V_4)=(omega^2, omega).
```

Both fixed-space projectors vanish in every pair, so each pair has a promised
zero-defect exact extension with `J=omega`.  Tensor the four ordinary-group
representations.  Exact group relations are tensor closed, and the central
character returns to the same sector because `omega^4=omega`.  But the
interface scalars multiply to

```text
u=omega^(1+1+2+2)=1,       v=omega^4=omega.
```

Thus the tensor product is a zero-defect representation in the soundness
sector with `Pi_0(u)=1` and `Pi_0(v)=0`.  Inequality `(PS3-1)` would read
`1<=0`.  Fixed amplification does not change the argument.

This obstruction is categorical, not implementation-specific: the visible
relation `Pi_0(U)=Pi_0(V)` is not tensor closed inside the nontrivial central
sector, whereas restrictions of exact ordinary-group representations are.
Noncommuting auxiliaries, additional finite packets, or a cyclic
sum-of-squares certificate cannot repair the proposed endpoint without
weakening its exact completeness or changing the carrier architecture.

The qutrit splice therefore connects cohesively to the independent-set
compiler at the shared hybrid rank router:

```text
moment-exact positive ONE3
 -> one qutrit clock per clause
 -> five-edge diamond overlap energies
 -> authenticated rank-conjugacy cells
 -> ordinary group relators.
```

The qutrit clauses and diamond remain useful established reductions.  The
only surviving groupification burden in this combined lane is the same
affine hybrid-block router already isolated by the independent-set route.
