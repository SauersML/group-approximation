# Orthogonal transfer formula for real and integral fillings

Date: 2026-08-11

## 1. Outcome

The orbit-average estimate in
`FALSE_NONAMENABLE_STABILIZER_FILLING_REDUCTION.md` admits an exact
orthogonal refinement.  For a finite regular intermediate cover of degree
`m`, the minimum real filling of a marked loop splits as

`Fill_R(b_up)^2`
` =m^(-1)Fill_R(b_down)^2+Fill_R((1-P)b_up)^2`.       `(OTF1)`

For the stable Laurent double, property `(T)` bounds the second summand by
one constant independent of the cover.  Thus

`Fill_R(b_up)^2=m^(-1)Fill_R(b_down)^2+O(1)`.          `(OTF2)`

There is also an integral transfer inequality.  Every integral filling
upstairs pushes to an integral filling downstairs, and orthogonal
projection onto deck invariants gives

`Fill_Z(b_up)^2>=m^(-1)Fill_Z(b_down)^2`.              `(OTF3)`

Combining `(OTF1)--(OTF3)` with the exact discriminant Pythagoras formula
transfers the canonical integral-repair radius:

`rho_up(c_up)^2`
` >=m^(-1)rho_down(c_down)^2`
`   -Fill_R((1-P)b_up)^2`.                             `(OTF4)`

In the Kazhdan-stabilizer tower the last term is uniformly bounded.  The
continuous and integral parts of the remaining obstruction are therefore
both reduced to the intermediate cover, with the sharp square-root loss.
This is the filling analogue of the exact nonlinear discriminant-repair
identity: the continuous minimum and the integral discriminant correction
remain paired rather than being estimated separately.

This note does not prove FALSE.  A large radius in `(OTF4)` is only an
integral-repair obstruction; one must still show that its paired marked
character makes the ratio in
`FALSE_MARKED_DISCRIMINANT_DIVERGENCE_CRITERION.md` unbounded.

## 2. Equivariant filling notation

Let

`p:Y_up->Y_down`                                      `(OTF5)`

be a finite regular cover of finite cellular complexes with deck group
`A` of order `m`.  Give the real cellular chain groups their standard
Euclidean norms.  Write

`P=(1/m)sum_(a in A)a`                                `(OTF6)`

for the orthogonal projection onto the invariant cellular chains, and let

`p_!:C_*(Y_down,R)->C_*(Y_up,R)`                      `(OTF7)`

be constant lift, the sum of all lifts of each cell.  On cellular chains,

`P=(1/m)p_!p_*`,
`||p_!z||_2^2=m||z||_2^2`.                            `(OTF8)`

Let `b_up` be one lift of a cellular one-cycle `b_down`, and suppose that
`b_up` is a real boundary.  Then both `Pb_up` and `(1-P)b_up` are real
boundaries because cellular boundary commutes with `P`.  Put

`epsilon_A(b_up)=Fill_R,2((1-P)b_up;Y_up)`.            `(OTF9)`

## 3. Exact orthogonal real splitting

**Theorem 1 (orthogonal filling decomposition).**  In the notation above,

`Fill_R,2(b_up;Y_up)^2`
` =Fill_R,2(Pb_up;Y_up)^2+epsilon_A(b_up)^2`           `(OTF10)`

and

`Fill_R,2(Pb_up;Y_up)`
` =m^(-1/2)Fill_R,2(b_down;Y_down)`.                   `(OTF11)`

Consequently `(OTF1)` holds exactly.

**Proof.**  The orthogonal decomposition

`C_2(Y_up,R)=P C_2 directSum (1-P)C_2`                `(OTF12)`

is preserved by cellular boundary.  Hence every filling `z` of `b_up`
decomposes uniquely into fillings

`Pz` of `Pb_up`, `(1-P)z` of `(1-P)b_up`.             `(OTF13)`

Conversely, the sum of any two such fillings fills `b_up`.  The two
summands in `(OTF12)` are orthogonal, so minimizing their squared norms is
independent and proves `(OTF10)`.

The invariant chains are precisely the constant lifts.  Since

`Pb_up=(1/m)p_!b_down`,                               `(OTF14)`

every invariant filling of `Pb_up` has the form

`(1/m)p_!z_down`, `partial z_down=b_down`.            `(OTF15)`

Its norm is `m^(-1/2)||z_down||` by `(OTF8)`.  Taking the minimum proves
`(OTF11)`.  End proof.

If a property-`(T)` subgroup supplies the uniformly bounded noninvariant
decoder of Theorem 3 in
`FALSE_NONAMENABLE_STABILIZER_FILLING_REDUCTION.md`, then that decoder may
be replaced by its `(1-P)` component.  Therefore

`epsilon_A(b_up)<=C`                                  `(OTF16)`

with one cover-independent `C`, and `(OTF2)` follows.

## 4. Integral pushdown

Assume now that `b_up` is an integral boundary.  Constant lift need not
carry an integral filling of `b_down` to a filling of the single lift
`b_up`; this is exactly where the rational average and integral repair
separate.  Pushdown nevertheless gives a sharp one-sided inequality.

**Theorem 2 (integral transfer inequality).**

`Fill_Z,2(b_up;Y_up)^2`
` >=m^(-1)Fill_Z,2(b_down;Y_down)^2`.                  `(OTF17)`

**Proof.**  Let `z` be any integral filling of `b_up`.  Then `p_*z` is an
integral filling of `b_down`.  By `(OTF8)`,

`Pz=(1/m)p_!p_*z`,
`||Pz||_2^2=m^(-1)||p_*z||_2^2`.                     `(OTF18)`

Orthogonal projection is contractive, hence

`||z||_2^2>=||Pz||_2^2`
`          >=m^(-1)Fill_Z,2(b_down)^2`.               `(OTF19)`

Minimize over integral `z`.  End proof.

The statement uses unnormalized cellular norms.  It is precisely invariant
under normalized norms: dividing both squared norms by the number of cells
removes the factor `m`.

## 5. Canonical discriminant classes commute with pushdown

For either complex, let `q` be the unique minimum real filling of the
corresponding loop.  For an integral filling `z`, write

`z=q+u`, `u in ker(partial_2)_R`.                      `(OTF20)`

The class

`c=u+ker(partial_2)_Z`
`  in ker(partial_2)_Z^#/ker(partial_2)_Z`             `(OTF21)`

is independent of `z`, and

`Fill_Z,2(b)^2=Fill_R,2(b)^2+rho(c)^2`.               `(OTF22)`

This is the exact discriminant Pythagoras identity from
`FALSE_REAL_FILLING_ESCAPE_DICHOTOMY.md`.

Let `q_up,q_down` and `c_up,c_down` denote these objects in `(OTF5)`.

**Proposition 3 (pushdown of the canonical class).**

`p_*q_up=q_down`.                                     `(OTF23)`

For every integral filling `z_up=q_up+u_up`, the cycle

`p_*u_up=p_*z_up-q_down`                              `(OTF24)`

represents `c_down`.  Thus the marked canonical discriminant class upstairs
pushes to the marked canonical discriminant class downstairs.

**Proof.**  By Theorem 1, the invariant part of `q_up` is the unique
minimum invariant filling

`Pq_up=(1/m)p_!q_down`.                               `(OTF25)`

The noninvariant part has pushdown zero, while `p_*p_!=m`; hence
`p_*q_up=q_down`.  Now push `(OTF20)` down.  The chain `p_*z_up` is an
integral filling downstairs, so its difference from `q_down` is exactly a
representative of the canonical class `(OTF21)` there.  Equation `(OTF23)`
identifies that difference with `p_*u_up`, proving the claim.  End proof.

## 6. Exact discriminant-transfer lower bound

**Theorem 4 (paired integral-repair transfer).**  The canonical radii obey

`rho_up(c_up)^2`
` >=m^(-1)rho_down(c_down)^2-epsilon_A(b_up)^2`.       `(OTF26)`

Equivalently,

`rho_down(c_down)^2`
` <=m(rho_up(c_up)^2+epsilon_A(b_up)^2)`.              `(OTF27)`

**Proof.**  Apply `(OTF22)` upstairs and downstairs.  Theorem 2 gives

`Fill_R(b_up)^2+rho_up(c_up)^2`
` >=m^(-1)(Fill_R(b_down)^2+rho_down(c_down)^2)`.      `(OTF28)`

Substitute the exact real splitting `(OTF1)` and cancel
`m^(-1)Fill_R(b_down)^2`.  What remains is `(OTF26)`.  End proof.

This cancellation is the important point.  Estimating the real and
integral filling norms independently loses the canonical discriminant
term.  Their exact Pythagorean decompositions retain it with the optimal
square-root scaling.

## 7. Application to the Kazhdan stabilizer tower

Use the notation of the stable Laurent double from
`FALSE_NONAMENABLE_STABILIZER_FILLING_REDUCTION.md`:

`K_n=pi^(-1)(L_n)`, `H_n=pi^(-1)(J L_n)`,
`m_n=[H_n:K_n]=|J/(J intersect L_n)|`.                `(OTF29)`

The cover `Y_(K_n)->Y_(H_n)` is regular of degree `m_n`.  The Kazhdan
decoder gives `epsilon_n<=C`.  Therefore

`Fill_R(b_(K_n))^2`
` =m_n^(-1)Fill_R(b_(H_n))^2+epsilon_n^2`,            `(OTF30)`

`rho_(K_n)(c_(K_n))^2`
` >=m_n^(-1)rho_(H_n)(c_(H_n))^2-C^2`.               `(OTF31)`

There are now two exact escape rates.

1. If `Fill_R(b_(H_n))/sqrt(m_n)` is unbounded, then the real-filling
   criterion proves FALSE.
2. If the real quotient stays bounded but
   `rho_(H_n)(c_(H_n))/sqrt(m_n)` is unbounded, then the canonical integral
   correction upstairs diverges by `(OTF31)`.

The second item does not alone prove FALSE.  By the exact nonlinear repair
formula, it says that the surviving obstruction lies in a paired
discriminant-Voronoi class, not in the continuous Hodge minimum.  The live
task is to show that this transferred class has a nonzero marked pairing
whose numerator grows relative to its exact paired well.  Proposition 3
ensures that this is one coherent marked class across the two levels rather
than an unrelated shortest-vector choice.

## 8. Status

Theorems 1, 2, and 4 are exact.  They strengthen the earlier additive
estimate to a Pythagorean identity and identify the sharp arithmetic loss
under intermediate transfer.

For the explicit FALSE program the remaining question is now self-contained:

> Can one choose mixed finite quotients `L_n normal F` for which the marked
> canonical discriminant class in `Y_(H_n)` has a nonzero transferred word
> pairing and paired repair ratio growing faster than `sqrt(m_n)`?

A positive answer proves FALSE through the marked discriminant divergence
criterion.  A uniform negative answer would be a genuine integral decoder
theorem for the invariant transfer mode.
