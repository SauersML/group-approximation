# The SL3 fold Gram: automatic polar alignment versus endpoint modulus

## Outcome

Lin's positive-cross-Gram common-PVM theorem cannot itself produce the
balanced-projection endpoint needed for the SL3 arithmetic double.  For any
two projections `P,Q`, the choice `G=PQ` already intertwines the complete
binary PVM packets with zero error.  At the canonical fold midpoint it has
fixed normalized mass `1/4`, even though the endpoint distance is maximal.

The datum discarded by polar gauging is the non-idempotence of the Gram
square

```text
d=tr(QPQ-(QPQ)^2)=(1/2)||[P,Q]||_2^2.
```

Vanishing `d`, not positive Gram mass, yields a fixed-density near-common
sector.  A residually finite `C_2*Z` tower shows this distinction is sharp in
exact finite matrices while every fixed local lamp word has its canonical
trace.

More strongly, in every hypothetical canonical microstate sequence of the
actual arithmetic swap extension, the fold word has Haar spectral law and
the Gram square is forced to the same half-arcsine distribution.  Hence the
actual canonical class fixes `d->1/16`; it does not merely fail to control
`d`.

## 1. The packet condition is an identity

Let `P,Q` be projections and set `G=PQ`.  For the binary packets

```text
P_1=P,       P_0=I-P,
Q_1=Q,       Q_0=I-Q,
```

one has

```text
P_1G=G=GQ_1,               P_0G=0=GQ_0.
```

Therefore

```text
sum_(a=0,1)||P_aG-GQ_a||_2^2=0
```

for every pair `P,Q`, and

```text
||G||_2^2=tr(QPQ)=tr(PQ).
```

The positive-cross-Gram theorem can only conclude alignment after replacing
`Q` by its polar gauge relative to `PQ`.  That gauge is precisely allowed to
rotate every principal-angle block and therefore contains no information
that `Q` was close to `P` in the original coordinates.

For balanced projections the fold trace is

```text
tr((I-2P)(I-2Q))=4tr(PQ)-1.
```

The canonical trace-zero fold condition therefore gives

```text
tr(PQ)->1/4,
||P-Q||_2^2=1-2tr(PQ)->1/2.
```

So the Gram has uniformly positive mass and perfect label covariance at the
same time that the desired endpoint is uniformly far away.

## 2. The missing modulus and the correct spectral implication

Set

```text
H=G^*G=QPQ,
m=tr(H),
d=tr(H-H^2).
```

Using cyclicity,

```text
d=tr(PQ)-tr(PQPQ)=(1/2)||[P,Q]||_2^2.
```

For `0<epsilon<1`, let `R=1_[1-epsilon,1](H)`.  Since `H=QHQ` and the
cut avoids zero, `R<=Q`.  On the complementary spectral interval,
`x<=epsilon^(-1)x(1-x)`, so

```text
m
 =tr(HR)+tr(H(I-R))
 <=tr(R)+d/epsilon.
```

Thus

```text
tr(R)>=m-d/epsilon.
```

Moreover, because `R<=Q` and `R` commutes with `H`,

```text
||(P-Q)R||_2^2
 =tr(R(P-Q)^2R)
 =tr(R(I-H)R)
 <=epsilon tr(R).
```

If `m>=m_0` and `d->0`, choosing `epsilon=sqrt(d)` gives a subprojection of
trace at least `m_0-o(1)` on which `P-Q` tends to zero.  This is the valid
positive-sector compiler.  The commuting-conjugate lamp route has `d=0`
exactly.  The arbitrary projective route has no known estimate on `d`.

## 3. The actual canonical swap class forces the half-arcsine law

In the swap extension

```text
E=<A,s | s^2=1,[s,C]=1>,
```

round the swap matrix to an exact involution `S`, put

```text
T=HSH^*,       V=TS,       P=(I-S)/2,       Q=(I-T)/2.
```

The word `v=hsh^(-1)s` is the product of two distinct free binary lamps in
the coset-wreath normal form.  It has infinite order.  Consequently full
canonicality gives

```text
tr(V_n^k)->0       for every fixed nonzero k,
```

so the spectral measures of `V_n` converge to Haar measure on the circle.
The two-projection principal-angle decomposition has generic blocks

```text
spec(V)={e^(2i theta),e^(-2i theta)},
spec(QPQ)={0,cos(theta)^2}.
```

The exceptional intersection blocks vanish in density because Haar measure
has no atoms at `+1` or `-1`.  Pushing Haar measure through
`z |->(2+z+conjugate(z))/4` therefore yields

```text
mu_(QPQ)=>(1/2)delta_0+(1/2)Arcsine_[0,1].
```

In particular,

```text
d=(1/16)(1-Re tr(V^2))->1/16,
```

and every moving window `[1-epsilon_n,1]`, `epsilon_n->0`, has vanishing
mass.  This is a theorem about any hypothetical canonical microstate sequence
of the full arithmetic swap presentation.  Therefore forcing `d->0` is
already a direct contradiction to its second canonical fold moment.

## 4. Exact finite sharpness with canonical local moments

Let

```text
Gamma=<s,h | s^2=1>=C_2*Z,
t=hsh^(-1).
```

Normal form gives `<s,t>=C_2*C_2`.  Because `Gamma` is residually finite,
there are finite quotients `q_n:Gamma->Gamma_n` injective on the radius-`n`
ball.  In the left regular representation of `Gamma_n`, define

```text
P_n=(I-lambda_n(q_n(s)))/2,
Q_n=lambda_n(q_n(h))P_n lambda_n(q_n(h))^*.
```

For every fixed nonidentity word `w in Gamma`,

```text
tr(lambda_n(q_n(w)))=0
```

for all sufficiently large `n`.  Thus this is a canonical-character
microstate tower for the entire local conjugator group, not merely a match
of finitely many scalar overlaps.

In the limit, `P,Q` are free projections of trace `1/2`.  The compression
`QPQ` has the arcsine distribution in the normalized `Q`-corner, and is zero
on the complementary half:

```text
mu_(QPQ)=(1/2)delta_0+(1/2) [dx/(pi sqrt(x(1-x)))]_(0,1).
```

It follows that

```text
tr(PQ)=1/4,
tr(PQPQ)=3/16,
d=1/16,
mu_(QPQ)([1-epsilon,1])=(1/pi)arcsin(sqrt(epsilon)).
```

In particular, for every `epsilon_n->0`, the fraction of singular directions
with squared singular value at least `1-epsilon_n` tends to zero.  Yet
`G_n=P_nQ_n` has mass `1/4+o(1)` and exactly zero binary-label intertwining
energy.

## 5. Consequence for the arithmetic route

This local tower is not an approximate representation of the full
`SL_3(Z[1/2])` actor and hence is not a counterexample to projective transfer.
Its role is to rule out an analytic non sequitur after the Lin package was
introduced:

```text
positive Gram mass + binary packet covariance
    does not imply
an original-coordinate fold sector or endpoint.
```

A successful arithmetic use of the package must add a same-Gram mixed return
which forces one of the following kinds of information, each contradicting
the canonical half-arcsine profile:

1. `tr(H-H^2)->0` (principal-angle concentration at `0` and `1`);
2. a fixed amount of spectral mass of `H` tending to `1`;
3. an original-coordinate estimate on the polar gauge;
4. in the native lamp presentation, approximate commutation of `P` and `Q`.

The first option is the smallest scalar target.  Merely exactifying the PVM
labels, preserving an opposite algebra, or extracting a positive mid-spectrum
corner leaves the forbidden canonical midpoint untouched.
