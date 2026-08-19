# Deck Fourier frames and an exact binary reduction at the prime two

Date: 2026-08-11

## 1. Outcome

There are two complementary conclusions.

First, the marked orbit-frame estimate admits a Fourier refinement.  Let
`X=D/K` be a finite regular presentation cover, let `q` be the canonical
minimum real filling of the marked loop at the identity vertex, and let
`A` be a finite abelian deck subgroup of order `m`.  If `P_chi` is the
orthogonal projection onto the `chi`-eigenspace in the complexified
two-chain space, then

`Lambda_(w,X)>=sqrt(m)||P_chi q||`                     `(DFB1)`

for every character `chi in A^`.  Consequently, bounded marked ratio can
coexist with a real filling of fixed positive norm only if its deck Fourier
mass is spread across a positive proportion of the characters of every
large abelian deck frame.

Second, in the fixed-prime Laurent tower at `p=2`, the radical homology
class is exactly anti-invariant under a canonical deck involution.  Write
`b_n` for the marked loop and `tau_n` for the involution.  Define

`S_n^+={s:tau_n s=s, d s=b_n+tau_n b_n}`,
`S_n^-={a:tau_n a=-a, d a=b_n-tau_n b_n}`.             `(DFB2)`

Then integral fillings of `b_n` are in exact bijection with pairs

`(s,a) in S_n^+ times S_n^-`, `s=a mod 2`,             `(DFB3)`

and orthogonality of the two eigenspaces gives

`Fill_Z,2(b_n)^2`
` =(1/4) min_(s,a satisfying (DFB3))`
`              (||s||^2+||a||^2).`                    `(DFB4)`

Thus the residual integral escape at the prime two is not an unspecified
large discriminant.  It lies exactly in one of three places: the invariant
filling radius, the anti-invariant filling radius, or the binary parity
gluing between two otherwise bounded sectors.  This gives a concrete
two-sector binary code to which the carry-incidence criterion can be
applied.

The statements do not by themselves prove FALSE.  The remaining task is
to show that the parity-glued sector in `(DFB3)` has an unbounded marked
incidence profile, or that bounded incidence would produce a bounded
compatible pair and contradict integral escape.

## 2. Fourier refinement of the orbit frame

Use the notation of
`FALSE_STABILIZER_FRAME_AMPLIFICATION.md`.  The marked analysis operator is

`T_X:W_X->R^X`,
`(T_X y)_x=<q_(w,x),y>`,                               `(DFB5)`

and the tangent estimate is

`Lambda_(w,X)>=||T_X||_op`.                            `(DFB6)`

Complexify `W_X` and `T_X`.  The operator norm is unchanged by
complexification.  Let `A` be a finite abelian deck subgroup, `|A|=m`, and
for `chi in A^` put

`P_chi=(1/m) sum_(a in A) conjugate(chi(a)) a.`         `(DFB7)`

Then `P_chi` is an orthogonal projection and

`a P_chi=chi(a)P_chi`.                                 `(DFB8)`

Write `q_chi=P_chi q`.

**Theorem 1 (deck Fourier-frame bound).**  For every `chi in A^`, equation
`(DFB1)` holds.

**Proof.**  The `m` vertices indexed by `A` are distinct because the deck
action on a regular cover is free.  Equivariance and uniqueness of the
minimum real filling give

`q_(w,a)=a q`.                                         `(DFB9)`

For every `a in A`, unitarity, `(DFB8)`, and orthogonality of `P_chi`
give

`|<a q,q_chi>|`
` =|<q,a^(-1)q_chi>|`
` =|<q,q_chi>|`
` =||q_chi||^2.`                                      `(DFB10)`

Therefore at least `m` coordinates of the complexified vector
`T_X q_chi` have modulus `||q_chi||^2`, and

`||T_X q_chi||>=sqrt(m)||q_chi||^2.`                  `(DFB11)`

If `q_chi!=0`, divide by its norm and use `(DFB6)`.  The zero case is
immediate.  End proof.

Because the character projections are pairwise orthogonal and sum to the
identity on the `A`-cyclic subspace of `q`,

`sum_(chi in A^)||P_chi q||^2=||q||^2.`               `(DFB12)`

This gives a useful necessary condition for bounded marked ratio.

**Corollary 2 (spectral delocalization).**  If

`Lambda_(w,X)<=C`,                                    `(DFB13)`

then

`||P_chi q||^2<=C^2/m`                                `(DFB14)`

for every character.  If `q` has at least `s>0` norm, the number of
nonzero character components is at least

`m s^2/C^2`.                                          `(DFB15)`

Thus along abelian deck groups of growing order, bounded `Lambda` forces
the Fourier support of every uniformly nonzero canonical filling to occupy
a positive fraction of the dual group.  Concentration on `o(m)`
characters proves FALSE.

**Proof.**  Equation `(DFB14)` is the square of `(DFB1)`.  Sum `(DFB14)`
over the nonzero components and use `(DFB12)`.  End proof.

The invariant-frame theorem is the special case `chi=1`.  The new content
is that every one-dimensional isotypic component is separately visible,
with the same `sqrt(m)` amplification.

## 3. The cyclotomic radical orbit at every prime

The prime-two involution below is the first member of a uniform
cyclotomic phenomenon.  Keep the stable Laurent notation

`h=e_12(x_1^(-1))`, `w=i_2(h)i_1(h)^(-1)`,
`B_p=E(p)`, `K_p=pi^(-1)(B_p)`,                       `(CYC1)`

and let `t=i_1(h)` in the first vertex copy.  Since elementary root
elements add their parameters,

`h^p=e_12(p x_1^(-1)) in B_p`,                        `(CYC2)`

whereas `h^k notin B_p` for `1<=k<p`.  The coefficient kernel `B_p` is
invariant under the Laurent exponent action, hence normal in `F`.
Therefore `t` normalizes `K_p` and induces a deck transformation of order
exactly `p`.

The `p` double cosets

`B_p h^k Gamma`, `0<=k<p`,                            `(CYC3)`

are pairwise distinct.  Indeed equality for `a!=b mod p` would put
`h^(a-b)` in `B_p Gamma`.  Reduction modulo `p` would then put the Laurent
monomial `(a-b)x_1^(-1)` in the polynomial ring
`F_p[x_1,...,x_d]`, which is impossible.

The Bass--Serre relation-module identification sends `[w]` to

`e_h=delta_(h Gamma)-delta_Gamma`.                     `(CYC4)`

For `0<=k<p`, its `k`-th deck translate maps in the free double-coset
module to

`t^k e_h`
` |->delta_(B_p h^(k+1) Gamma)-delta_(B_p h^k Gamma).` `(CYC5)`

These are the oriented edges of a `p`-cycle.

**Theorem 3 (cyclotomic limiting class).**  The deck orbit of `[w]` in
`H_1(K_p,Z)` generates a copy of the integral augmentation lattice

`Aug_Z(C_p)=ker(Z[C_p]->Z)`.                           `(CYC6)`

It has rank `p-1`; after complexification, every nontrivial character of
`C_p` occurs once and the trivial character does not occur.

**Proof.**  The sum of the orbit elements telescopes to

`delta_(B_p h^p Gamma)-delta_(B_p Gamma)=0`,           `(CYC7)`

so their span has rank at most `p-1`.  Their images in the free module on
the `p` distinct points `(CYC3)` are the standard cycle differences and
have rank `p-1`.  Hence there are no further relations.  The split
abelianization identifies the radical summand of `H_1(K_p,Z)` with the
relevant coinvariant module.  End proof.

This supplies cyclic deck frames of arbitrarily large prime order if the
prime is allowed to vary.  Along a diagonal family with `p->infinity`,
Corollary 2 says that bounded marked ratio forces every uniformly nonzero
canonical real filling to distribute its mass across linearly many
cyclotomic characters.  Concentration on `o(p)` characters proves FALSE.

## 4. The canonical involution at `p=2`

Now use the stable Laurent double

`pi:D=G *_Gamma G -> F=G *_E G`,                      `(DFB16)`

with

`R=Z[x_1^(+-1),...,x_d^(+-1)]`,
`E=EL_r(R)`,
`Gamma=EL_r(Z[x_1,...,x_d])`,                         `(DFB17)`

and

`h=e_12(x_1^(-1))`,
`w=i_2(h)i_1(h)^(-1)`.                                `(DFB18)`

Fix `p=2` and let

`B=E(2)=ker(E->EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]))`,
`K_infinity=pi^(-1)(B)`.                              `(DFB19)`

Let `t=i_1(h)` in the first vertex copy.  Since elementary root elements
add their parameters,

`h^2=e_12(2x_1^(-1)) in B`,                           `(DFB20)`

whereas `h notin B`.  The subgroup `B` is normal in `E`, so `t` normalizes
`K_infinity` and its induced deck transformation has order two.

The Bass--Serre relation-module identification from
`FALSE_INTERMEDIATE_SPLIT_HOMOLOGY.md` sends

`[w]` to `e_h=delta_(h Gamma)-delta_Gamma`.            `(DFB21)`

After taking `B`-coinvariants,

`t e_h`
` =delta_(B h^2 Gamma)-delta_(B h Gamma)`
` =delta_(B Gamma)-delta_(B h Gamma)`
` =-e_h.`                                              `(DFB22)`

The class `e_h` has infinite order because `h notin B Gamma`, as proved in
the fixed-prime tower note.  Hence:

**Corollary 4 (anti-invariant limiting class).**  The infinite-order class
of `w` in `H_1(K_infinity,Z)` is a `-1` eigenvector for the involution
induced by `t`.

This is stronger than saying that the class merely survives at the prime
two: its exact deck representation type is determined.

## 5. A fixed symmetric filling

Corollary 4 implies

`[w]+t[w]=0 in H_1(K_infinity,Z)`.                     `(DFB23)`

Equivalently, the group element

`u=w(twt^(-1))`                                       `(DFB24)`

lies in `[K_infinity,K_infinity]`.  In the cellular cover of the fixed
finite presentation, the one-chain of `(DFB24)` is exactly

`b_infinity+t b_infinity`.                            `(DFB25)`

Indeed the initial `t`-path and terminal `t^(-1)`-path in the conjugate
cancel as cellular one-chains because `w` is a loop.  Therefore there is a
finite-support integral two-chain `S_infinity` with

`d S_infinity=b_infinity+t b_infinity`.               `(DFB26)`

Take the nested fixed-prime subgroups `L_n` from
`FALSE_FIXED_PRIME_CONSTANT_STABILIZER_TOWER.md` and put

`K_n=pi^(-1)(L_n)`.                                   `(DFB27)`

Because `B<=L_n`, the chain `S_infinity` projects to an integral chain
`S_n` in every finite cover.  Because `L_n` is normal in `F`, `t` acts as a
deck transformation there; `(DFB20)` says that it is an involution.  A
quotient can merge finitely many coefficients, but its `L2` norm is bounded
by the fixed `L1` norm upstairs.  We obtain

`d S_n=b_n+tau_n b_n`,
`sup_n||S_n||<=||S_infinity||_1`.                      `(DFB28)`

Thus the symmetric translated boundary is uniformly integrally fillable,
even though

`Fill_Z,2(b_n)->infinity`.                             `(DFB29)`

The latter is the fixed-prime integral escape theorem.

## 6. Exact invariant/anti-invariant parity gluing

Let

`F_n={z in C_2(X_n,Z):d z=b_n}`.                      `(DFB30)`

The two affine eigenspace sets `S_n^+` and `S_n^-` were defined in
`(DFB2)`.

**Theorem 5 (binary eigenspace-gluing bijection).**  The map

`F_n -> S_n^+ times S_n^-`,
`z |->(z+tau_n z,z-tau_n z)`                          `(DFB31)`

is a bijection onto the pairs `(s,a)` satisfying the single compatibility
condition

`s=a mod 2`.                                          `(DFB32)`

Its inverse is

`(s,a) |->(s+a)/2`.                                   `(DFB33)`

Moreover the two terms are orthogonal, and `(DFB4)` holds.

**Proof.**  If `d z=b_n`, put `s=z+tau_n z` and
`a=z-tau_n z`.  Then

`tau_n s=s`, `d s=b_n+tau_n b_n`,
`tau_n a=-a`, `d a=b_n-tau_n b_n`.                    `(DFB34)`

Also `s-a=2 tau_n z`, proving `(DFB32)`.  Conversely, if `s` and `a`
satisfy `(DFB2)` and `(DFB32)`, then `(s+a)/2` is integral and

`d((s+a)/2)=b_n`.                                     `(DFB35)`

The eigenspace identities show that applying `(DFB31)` recovers `(s,a)`.
Finally

`<s,a>=<tau_n s,tau_n a>=<s,-a>=-<s,a>`,             `(DFB36)`

so `<s,a>=0` and

`||(s+a)/2||^2=(1/4)(||s||^2+||a||^2)`.              `(DFB37)`

Minimizing proves `(DFB4)`.  End proof.

This is an exact integral Pythagoras theorem.  Over the reals the two
equations split orthogonally with no interaction.  Over the integers they
can be reassembled precisely when their coordinate parities agree.  The
only coupling between the two deck eigenspaces is therefore binary.

For comparison, the fixed chain `S_n` from `(DFB28)` gives a one-sided
coordinate form.  Integral fillings of `b_n` are also in bijection with

`z^- in C_2(X_n,Z)`,
`d z^-=b_n-tau_n b_n`, `z^-=S_n mod 2`,               `(DFB38)`

via `z=(S_n+z^-)/2`.  This form is useful for computation, but by itself it
is only an affine reparametrization.  The structural statement is the
eigenspace condition `(DFB32)` and the orthogonal identity `(DFB4)`.

**Corollary 6 (three-way escape dichotomy).**  Put

`I_n^+=min_(s in S_n^+)||s||`,
`I_n^-=min_(a in S_n^-)||a||`.                         `(DFB39)`

After passing to a subsequence, integral escape `(DFB29)` has one of the
following causes.

1. `I_n^+->infinity`.
2. `I_n^-->infinity`.
3. Both `I_n^+` and `I_n^-` remain bounded, but the minimum in `(DFB4)`
   over parity-compatible pairs diverges.

In the third case, each eigenspace separately has a bounded integral
filling, and the obstruction is entirely the absence of a bounded pair
with the same reduction modulo two.

**Proof.**  Pass successively to subsequences on which each of `I_n^+` and
`I_n^-` is bounded or tends to infinity.  If both are bounded while the
left side of `(DFB4)` diverges, no bounded choices can satisfy `(DFB32)`.
End proof.

The real analogue is even sharper.  If `q_n` is the canonical minimum real
filling of `b_n`, then

`q_n=P_+q_n+P_-q_n`, `P_+=(1+tau_n)/2`,
`P_-=(1-tau_n)/2`,                                   `(DFB40)`

and `2P_+q_n`, `2P_-q_n` are the minimum real points in the affine spaces
underlying `S_n^+`, `S_n^-`.  The Fourier-frame theorem gives

`Lambda_(w,X_n)>=sqrt(2)||P_+q_n||`,
`Lambda_(w,X_n)>=sqrt(2)||P_-q_n||`.                  `(DFB41)`

Thus unbounded real escape in either sign sector proves FALSE.  In the
surviving bounded-real branch, both real eigensector fillings are bounded
and all divergence in Corollary 6 is integral arithmetic.

## 7. A bounded-weight primary cycle-lift obstruction

The third branch of Corollary 6 can be made into a single sparse-syndrome
decoder failure.  Suppose

`I_n^+<=C`, `I_n^-<=C`.                               `(DFB42)`

Choose `s_n^0 in S_n^+`, `a_n^0 in S_n^-` with norms at most `C`, and put

`epsilon_n=red_2(s_n^0-a_n^0)`.                       `(DFB43)`

Every nonzero coordinate of `epsilon_n` lies in the union of the supports
of `s_n^0` and `a_n^0`.  Since a nonzero integral coordinate contributes
at least one to squared Euclidean norm,

`weight(epsilon_n)<=2C^2`.                            `(DFB44)`

Let

`Z_n^+={u in C_2(X_n,Z):tau_n u=u, d u=0}`,
`Z_n^-={v in C_2(X_n,Z):tau_n v=-v, d v=0}`           `(DFB45)`

and define the integral lift cost of the binary syndrome by

`kappa_n(epsilon_n)`
` =min {sqrt(||u||^2+||v||^2):`
`         u in Z_n^+, v in Z_n^-,`
`         red_2(u-v)=epsilon_n}.`                     `(DFB46)`

The set in `(DFB46)` is nonempty: a finite-stage integral filling of
`b_n`, decomposed by Theorem 5, supplies a parity-compatible pair, and its
difference from `(s_n^0,a_n^0)` supplies `(u,v)`.

**Theorem 7 (sparse primary lift escape).**  In the third branch of
Corollary 6,

`weight(epsilon_n)<=2C^2`,
`kappa_n(epsilon_n)->infinity`.                        `(DFB47)`

**Proof.**  Every parity-compatible pair has the form

`(s_n^0+u,a_n^0+v)`, `u in Z_n^+`, `v in Z_n^-`,      `(DFB48)`

and compatibility is exactly the last condition in `(DFB46)`.  The product
Euclidean norm satisfies

`sqrt(||s_n^0+u||^2+||a_n^0+v||^2)`
` <=sqrt(2)C+sqrt(||u||^2+||v||^2).`                  `(DFB49)`

If `(DFB46)` stayed bounded, `(DFB49)` would give bounded compatible pairs,
contrary to the third branch and `(DFB4)`.  Equation `(DFB44)` proves the
support bound.  End proof.

Thus the genuinely hard parity branch is witnessed by binary syndromes of
uniformly bounded support whose integral invariant/anti-invariant cycle
lifts have unbounded norm.  This is exactly the type of bounded-primary
decoder failure that a fixed-resolution integral comparison theorem must
exclude.  In particular, a uniform decoder for the maps in `(DFB46)` rules
out branch 3 completely; it would leave only escape of one of the two sign
sector radii.

## 8. The remaining finite target

Theorem 5 turns the prime-two branch into a family of two-sector affine
binary gluing problems, and Theorem 7 makes the hardest branch a
bounded-weight lift failure.  The finite combinatorial target is now:

> prove that the parity-compatibility relation `(DFB32)` has carry
> incidence `a_n` and marked witness incidence `b_n` with `a_n/b_n->0`, or
> prove that bounded marked incidence produces a uniformly bounded
> parity-compatible pair.

The first alternative plugs directly into
`FALSE_BERNOULLI_CARRY_INCIDENCE.md` and proves FALSE.  The second would
contradict `(DFB4)` and `(DFB29)`.  What remains is a quantitative
incidence theorem; the group-theoretic source of the binary code, its deck
representation type, and its exact parity gluing are now explicit.
