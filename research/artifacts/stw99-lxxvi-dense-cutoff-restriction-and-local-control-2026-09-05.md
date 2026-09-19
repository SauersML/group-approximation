# Positive cutoff restriction has dense image, but lacks local control

Date: 5 September 2026. Internally reviewed.

Review record: the independent root audit checked the approximate
polar estimate 3 sqrt(e), the explicit CAR approximants, and the
conditional-expectation lower bound 3/4. No gap was found. Density
is explicitly a CEI prior-art consequence; no parameterized extension
theorem is asserted.

The density statement below is a consequence of prior art: the proof
of Coward--Elliott--Ivanescu, [*The Cuntz semigroup as an invariant for
C*-algebras*](https://arxiv.org/pdf/0705.0341), Theorem 3, printed
pages 28--29, proves approximate unitary equivalence of Hilbert-module
embeddings on finite sets. We give a direct frame proof with an error
bound, then an explicit obstruction to making these approximations
close to a prescribed larger frame. Neither result supplies the
parameterized positive-source extension needed beyond real rank zero.

## 1. Approximate transitivity with fixed Gram element

Let B be a C*-algebra, d in B_+, and C=Her(d). Assume C has stable
rank one. For b in B_+, put

```text
F(b,d)={v in closure(dB):v*v=b}.
```

If v_0,v belong to F(b,d), then

```text
v belongs to the norm closure of U(C~) v_0.                 (1.1)
```

Here C~ is its unitization, or C itself when C is unital; its
unitaries act on closure(dB). No simplicity, finiteness, purity,
real rank zero, or hereditary K-stability is needed.

To prove this, set x=v v_0* in C. Since v*v=v_0*v_0=b,

```text
x*x=v_0 b v_0*=(v_0v_0*)^2,       |x|=v_0v_0*.
```

Stable rank one supplies unitaries u in C~ for which
e=||u|x|-x|| is arbitrarily small: approximate x by invertibles
and use their polar unitaries, together with norm continuity of
the absolute-value map.

For completeness, the following estimate converts this to a frame
estimate without a spectral gap in b:

```text
||u v_0-v|| <= 3 sqrt(e).                                 (1.2)
```

When e>0, take polar decompositions v_0=V_0 b^(1/2) and
v=V b^(1/2) in a faithful representation, and put T=uV_0-V.
Both partial isometries have initial projection s(b); hence ||T||<=2.
The preceding error identity gives ||Tb||=e. If Q is the spectral
projection of b for [e,infinity), then

```text
||T b^(1/2)Q|| <= e/sqrt(e),
||T b^(1/2)(1-Q)|| <= 2 sqrt(e).
```

Their sum proves (1.2). If e=0, the same split at arbitrary positive
threshold proves T b^(1/2)=0. The representation is used only to
estimate norms; the resulting approximating frames remain in B.

## 2. Dense restriction from an existing larger embedding

Suppose a in B_+, b=(a-eta)_+ for eta>0, and F(a,d) is nonempty.
Define the continuous function

```text
h(t)=sqrt((t-eta)_+/t) for t>0,       h(0)=0.
```

The right Hilbert modules H_b=closure(bB) and H_a=closure(aB)
satisfy H_b contained in H_a. The frame w in F(a,d) represents the
embedding T_w:H_a->closure(dB) given by T_w(a^(1/2)z)=wz.
Because b^(1/2)=a^(1/2)h(a), actual restriction is

```text
rho:F(a,d)->F(b,d),       rho(w)=w h(a).                   (2.1)
```

**Dense restriction lemma.** If Her(d) has stable rank one and
F(a,d) is nonempty, then rho has norm-dense image.

Fix w_0 in F(a,d). Its restriction v_0=w_0h(a) has Gram b.
For any prescribed v in F(b,d), Section 1 gives unitaries u_n
with u_n v_0->v. The frames w_n=u_n w_0 still lie in F(a,d),
and rho(w_n)=u_n v_0. This proves density.

If B itself has stable rank one, its hereditary algebras have stable
rank one. Moreover [a]<=[d] in Cu(B) guarantees F(a,d) is nonempty:
the stable-rank-one module order theorem gives an embedding H_a->H_d,
whose value on a^(1/2) is the required frame. Thus the lemma applies
to arbitrary source cutoffs whenever [a]<=[d]; strict inequality
and hereditary K-stability are unnecessary for this pointwise result.

The same proof works with b=a^(1/2)h(a)^2 a^(1/2) whenever the
chosen continuous multiplier h(a) specifies the actual submodule
restriction and b^(1/2)=a^(1/2)h(a). The cutoff case above is the
only instance needed here.

## 3. Explicit approximants in the previous CAR example

Use the CAR diagonal and notation from
[the exact restriction counterexample](stw99-lxxvi-hereditary-k-stability-and-cutoff-restriction-2026-09-05.md):

```text
A=tensor M_2,       c=sum 2^(-n)e_n,
delta=1/4,       epsilon=1/2,
a=(c-delta)_+,       b=(c-epsilon)_+,
h(c)=sqrt(b/a), with the continuous zero extension.
```

The previous frame is
v(c)=sqrt((c-epsilon)_+) exp(i/(c-epsilon)) above epsilon,
zero below. For integers n>=2 set

```text
u_n(c)=exp(i/max(c-epsilon,1/n)),
w_n=a^(1/2)u_n(c).
```

These are continuous diagonal functional-calculus expressions,
w_n*w_n=a, and rho(w_n)=b^(1/2)u_n(c). This equals v wherever
c-epsilon>=1/n. On the remaining positive spectrum both terms
have norm at most 1/sqrt(n), so

```text
||rho(w_n)-v|| <= 2/sqrt(n).
```

The earlier failure of an exact lift is therefore compatible with
dense restriction, with an explicit approximation rate.

## 4. Dense image does not provide small corrections to a fixed lift

The following is a separate, stronger limitation on the proposed
iteration. Retain the CAR example and put

```text
w_0=a^(1/2),       v_0=b^(1/2),       rho(w_0)=v_0.
```

Choose a continuous real function chi on R with chi(s)=1 for
s<=1, chi(s)=0 for s>=2, and 0<=chi<=1. For 0<t<1/8 put

```text
u_t=exp(i pi chi((c-epsilon)/t)),
v_t=b^(1/2)u_t.
```

Each v_t has an exact larger lift a^(1/2)u_t. Also

```text
||v_t-v_0|| <= 2 sqrt(2t),
```

because the frames agree whenever c-epsilon>=2t and both vanish
below epsilon. Thus t->v_t, with value v_0 at t=0, is a norm
continuous family of cutoff frames.

Nevertheless, for every w in A satisfying

```text
||w h(c)-v_t|| <= sqrt(t)/2,
```

one has

```text
||w-w_0|| >= (3/2) sqrt(epsilon-delta+t) >= 3/4.            (4.1)
```

This does not require w*w=a. Let E:A->Delta be the diagonal
conditional expectation, and choose a diagonal point omega with
c(omega)=epsilon+t. At that point, chi(1)=1, so

```text
v_t(omega)=-sqrt(t),
w_0(omega)=sqrt(epsilon-delta+t),
h(c)(omega)=sqrt(t)/sqrt(epsilon-delta+t).
```

Contractivity and bimodularity of E give

```text
|E(w)(omega)h(c)(omega)+sqrt(t)| <= sqrt(t)/2.
```

Subtracting w_0(omega)h(c)(omega)=sqrt(t), then dividing by the
positive value of h(c)(omega), proves (4.1).

In particular, fix any r<3/4. The norm closure of
rho({w in F(a,1_A):||w-w_0||<r}) contains no neighborhood of v_0
in F(b,1_A). Indeed every sufficiently small v_t is excluded from
that closure by a target ball of radius sqrt(t)/2, while v_t->v_0.
Thus restriction need not be locally open, even after taking closure
of the image of a small source neighborhood.

Consequently, there is no continuous family w(t) with w(0)=w_0
whose restriction approximates v_t to error at most sqrt(t)/2 for
all sufficiently small t>0. This is a quantitative relative-error
obstruction, not a failure of approximation at a fixed uniform error.

## 5. Exact remaining mathematical gap

Pointwise norm density is settled positively and is prior art in
module form. It supplies neither continuous choices of the correcting
unitaries over a parameter space nor small corrections to the larger
frame. Section 4 disproves the latter assertion for arbitrary fixed
cutoffs, even when the prescribed small cutoff frames themselves have
exact lifts and converge to the restriction of a chosen base frame.

Hereditary K-stability may still allow a construction that changes
cutoff levels or controls only deeper source submodules during an
iteration. The present results do not rule that out. They also do not
rule out parameterized approximation with a fixed uniform tolerance.
No exact relative positive-source extension theorem beyond RR0 is
asserted here. The associated claim records only the density and
failure of local control proved above.
