# A bounded marked frame collapses paired carry to the cycle side

Date: 2026-08-12

## 1. Outcome

The exact paired carry energy

```text
delta(c)^2=min_d
  (rho_L(gamma(c-d))^2+rho_K(d)^2)                    (BPC1)
```

looks strictly more flexible than the original cycle radius `rho_K(c)`.
In a chart whose marked-word filling frame is uniformly bounded, that
extra flexibility disappears at the existential FALSE endpoint.

More precisely, let `N` be the number of marked-word coordinates and let

```text
Q:ell^2(X)->W,       Q delta_x=q_x,       |X|=N,      (BPC2)
```

be the synthesis operator of the canonical minimum real fillings of the
word.  If `||Q||<=C`, then every discriminant class satisfies

```text
mu_w(c)
 <=(2 pi C/sqrt(N)) rho_L(gamma(c)).                  (BPC3)
```

Here `mu_w` is the normalized chordal marked-word displacement.  Thus a
range-cheap class is automatically word-invisible.

If `d` realizes the minimum in `(BPC1)`, the triangle inequality gives

```text
rho_K(d)<=delta(c),
mu_w(d)>=mu_w(c)-(2 pi C/sqrt(N))delta(c).             (BPC4)
```

For covers of one fixed presentation, the number `m` of relator cells is a
fixed multiple of `N`.  Consequently

```text
there are c_n with delta(c_n)=o(sqrt(m_n))
and liminf mu_w(c_n)>0

iff

there are d_n with rho_K(d_n)=o(sqrt(m_n))
and liminf mu_w(d_n)>0.                               (BPC5)
```

So the paired infimal convolution can help *find* a low-energy class, but
under a bounded marked frame every successful paired witness contains an
ordinary cycle-cheap marked witness.  It gives no additional existential
route to a hyperlinear nonsofic image.

For the canonical cyclic direction the conclusion is sharper.  If `c_y`
is one canonical filling class, then

```text
mu_w(k c_y)<=2 pi C^2 |k|/sqrt(N).                    (BPC6)
```

Macroscopic cyclic amplification therefore requires `|k|=Omega(sqrt(N))`.
In particular the order of `c_y` must itself be `Omega(sqrt(N))`, not merely
tend to infinity.  This quantifies the high-order escape left open by
`FALSE_DISCRIMINANT_MULTIPLE_ESCAPE.md`.

Applied to the constant-stabilizer Kazhdan tower, the theorem removes the
range-cheap and hybrid paired branches.  The sole nonlinear target is now a
class which is simultaneously cycle-microscopic and marked-macroscopic;
if it is sought in the canonical cyclic direction, it must occur at
square-root-scale multiple and order.

## 2. Setup and the marked character

Let `Y_X` be a regular finite cover of a fixed presentation complex, with
deck set `X` of size `N`.  Let `m` be the number of relator two-cells.  For
a fixed presentation,

```text
m=rN                                                     (BPC7)
```

where `r` is the number of relators in the base presentation.

Write

```text
W=ran_R(d^1_X),
L=W intersect Z^m,
K=W^perp intersect Z^m,                                (BPC8)
```

and let

```text
gamma:D_K=K^#/K -> D_L=L^#/L                           (BPC9)
```

be the unimodular discriminant gluing.  Fix a word `w` in the sofic radical
of the presented group.  Its lift at `x in X` is an integral boundary, and
let

```text
q_x in W                                               (BPC10)
```

be its canonical minimum real filling.  The marked-frame synthesis is the
operator `(BPC2)`.

The explicit marked dual-class theorem in
`FALSE_RADICAL_FILLING_DISCRIMINANT.md` says that for every `c in D_K` and
every representative

```text
a in L^#,       a+L=gamma(c),                          (BPC11)
```

the `x`-th marked phase is

```text
chi_x(c)=<q_x,a> mod Z.                                (BPC12)
```

This is independent of the representative because `q_x in L^#`.

Define the normalized marked chordal seminorm

```text
mu_w(c)^2=(1/N)sum_(x in X)
 |exp(2 pi i chi_x(c))-1|^2.                           (BPC13)
```

It obeys the triangle inequality

```text
mu_w(c+c')<=mu_w(c)+mu_w(c')                           (BPC14)
```

because the scalar chordal length on the circle is subadditive and
Minkowski's inequality applies to the normalized `ell^2` sum.

Assume from now on that

```text
||Q||<=C.                                              (BPC15)
```

In the bounded-intermediate-real branch of the constant-stabilizer tower,
Theorem `(KOF4)` of `FALSE_KAZHDAN_ORBIT_FRAME_OPERATOR_BOUND.md` supplies
exactly `(BPC15)` with one `C` independent of the cover.

## 3. Range radius dominates the marked word

**Theorem 1 (range-to-word domination).**  Under `(BPC15)`, every
`c in D_K` satisfies `(BPC3)`.

**Proof.**  Choose `a` in `(BPC11)` with

```text
||a||=rho_L(gamma(c)).                                 (BPC16)
```

For every real number `t`,

```text
|exp(2 pi i t)-1|<=2 pi dist(t,Z)<=2 pi |t|.          (BPC17)
```

Equations `(BPC12)--(BPC13)` therefore give

```text
mu_w(c)^2
 <=(4 pi^2/N)sum_x |<q_x,a>|^2
 =(4 pi^2/N)||Q^*a||^2
 <=(4 pi^2 C^2/N)||a||^2.                             (BPC18)
```

Taking square roots and using `(BPC16)` proves `(BPC3)`.  End proof.

Two consequences are worth recording separately.

First, a macroscopic marked class is necessarily range-macroscopic:

```text
mu_w(c)>=eta
  ==> rho_L(gamma(c))>=eta sqrt(N)/(2 pi C).           (BPC19)
```

Second, `(BPC3)` has no phase-order hypothesis.  It controls high-order
clocks as well as binary classes.  The bounded-order incidence theorem in
`FALSE_BOUNDED_FRAME_PHASE_INCIDENCE_NO_GO.md` is finer at the level of
support, while `(BPC3)` is stronger at the level of total marked energy.

## 4. Exact paired-to-cycle extraction

Recall the exact paired carry energy `(BPC1)` from
`FALSE_PAIRED_CARRY_ENERGY.md`.  Since the discriminant group is finite, a
minimizer exists.

**Theorem 2 (paired witness extraction).**  Let `c in D_K`, and choose
`d in D_K` so that

```text
delta(c)^2
 =rho_L(gamma(c-d))^2+rho_K(d)^2.                     (BPC20)
```

Then `(BPC4)` holds.  More explicitly,

```text
rho_K(d)<=delta(c),                                    (BPC21)
mu_w(d)>=mu_w(c)-2 pi C delta(c)/sqrt(N).              (BPC22)
```

**Proof.**  Equation `(BPC21)` is immediate from `(BPC20)`.  Since
`c=(c-d)+d`, the triangle inequality `(BPC14)` gives

```text
mu_w(d)>=mu_w(c)-mu_w(c-d).                            (BPC23)
```

Apply Theorem 1 and then `(BPC20)`:

```text
mu_w(c-d)
 <=(2 pi C/sqrt(N))rho_L(gamma(c-d))
 <=(2 pi C/sqrt(N))delta(c).                          (BPC24)
```

Substitution into `(BPC23)` proves `(BPC22)`.  End proof.

Using `(BPC7)`, the loss may be written in normalized relator units as

```text
mu_w(d)>=mu_w(c)
 -2 pi C sqrt(r) delta(c)/sqrt(m).                    (BPC25)
```

This proves the promised equivalence.

**Corollary 3 (paired and cycle criteria are existentially equivalent).**
For a sequence of regular covers of one fixed presentation satisfying one
uniform marked-frame bound `(BPC15)`, the following are equivalent.

1. There are `c_n` such that

   ```text
   delta_n(c_n)/sqrt(m_n)->0,
   liminf_n mu_(w,n)(c_n)>0.                          (BPC26)
   ```

2. There are `d_n` such that

   ```text
   rho_(K,n)(d_n)/sqrt(m_n)->0,
   liminf_n mu_(w,n)(d_n)>0.                          (BPC27)
   ```

**Proof.**  Apply Theorem 2 stagewise to prove `1=>2`.  The marked lower
bound survives by `(BPC25)`, and `(BPC21)` gives the cycle-radius condition.
Conversely, take `c_n=d_n` and use

```text
delta_n(d_n)<=rho_(K,n)(d_n),                          (BPC28)
```

which follows by choosing the cycle-side term in `(BPC1)`.  End proof.

Thus the hybrid decomposition in the exact carry formula is useful for
finite optimization, but it cannot create a new asymptotic marked witness
when the marked frame is bounded.  Any successful hybrid output contains a
successful cycle-side output.

## 5. The square-root barrier for the canonical cyclic direction

Let `c_y` be the canonical filling class of the word at one deck vertex.
Its glued range class is represented by `q_y`:

```text
gamma(c_y)=q_y+L.                                      (BPC29)
```

For every integer `k`, the vector `kq_y` represents `gamma(kc_y)`, and
`||q_y||<=||Q||<=C`.  Hence

```text
rho_L(gamma(kc_y))<=|k|C.                              (BPC30)
```

Theorem 1 now gives `(BPC6)`:

```text
mu_w(kc_y)<=2 pi C^2 |k|/sqrt(N).                      (BPC31)
```

**Corollary 4 (square-root cyclic amplification barrier).**  If

```text
mu_w(k_n c_(y,n))>=eta>0,                              (BPC32)
```

then

```text
|k_n|>=eta sqrt(N_n)/(2 pi C^2).                       (BPC33)
```

If `h_n=ord(c_(y,n))`, choose every multiple using an integer representative
with `|k|<=h_n/2`.  The existence of any multiple satisfying `(BPC32)` then
forces

```text
h_n>=eta sqrt(N_n)/(pi C^2).                           (BPC34)
```

In particular:

```text
h_n=o(sqrt(N_n))
  ==> sup_(k in Z) mu_w(kc_(y,n))->0.                 (BPC35)
```

The bounded-multiple theorem in
`FALSE_DISCRIMINANT_MULTIPLE_ESCAPE.md` proves only `h_n->infinity` from
the topology of the limiting cover.  Equations `(BPC33)--(BPC35)` identify
the much stronger growth required if that same cyclic direction is to
retain the radical word in a phase microstate.

## 6. Consequences and remaining gate

In the bounded-real branch of the constant-stabilizer tower, the following
routes are now closed.

1. A range-cheap class cannot carry macroscopic marked energy by `(BPC3)`.
2. A paired range/cycle decomposition cannot evade the cycle criterion by
   Corollary 3.
3. Bounded or sub-square-root multiples of one canonical class cannot
   amplify the marked word by Corollary 4.
4. Canonical bounded-order dense incidence was already excluded in
   `FALSE_BOUNDED_FRAME_PHASE_INCIDENCE_NO_GO.md`.

The exact residual FALSE target is therefore a class `d_n` satisfying

```text
rho_(K,n)(d_n)=o(sqrt(m_n)),
mu_(w,n)(d_n)=Omega(1).                                (BPC36)
```

Theorem 1 automatically makes its glued range radius macroscopic.  If
`d_n` lies in the canonical cyclic direction, its multiplier and the order
of that direction must be at least square-root scale.

This does not prove that `(BPC36)` is impossible, and therefore does not
prove the universal hyperlinear-to-sofic implication.  It removes all
benefit of the paired range-side optimization after the Kazhdan marked
frame has been bounded, leaving one unambiguous cycle-lattice question.
