# A retuned exact omega model through Kassel (2.8), including (2.12)

The pair (2.7)--(2.8) charges the first explicit 24-dimensional packet, but
that collision is not representation-independent.  Here is a second
24-dimensional packet satisfying simultaneously

```text
(2.4), (2.5), (2.6), (2.7), (2.8), and (2.12)
```

with `w_beta^4=omega I`.

Put

```text
omega=exp(2 pi i/3),  nu=exp(-pi i/6),  q=nu^(-2)=exp(pi i/3).
```

## Retuned four-point packet

On `{0,1,2,3}`, set

```text
a=(1 2 3),
b=(0 1)(2 3),
d=(0 3)(1 2),
k=(1 3 2).
```

Direct multiplication gives

```text
[a,b]=d,       d^2=b^2=1,
ka=ak,         k d k^(-1)=d b^(-1).                    (P)
```

The last two identities are the retuning mechanism absent from the first
packet.

## Six-clock gauge

On `C^6`, let

```text
X e_j=e_(j+1),       Z e_j=q^(-j)e_j.
```

Thus `[X,Z]=qI`.  Define a diagonal unitary `H` by

```text
H e_j=h_j e_j,       h_j=nu^j q^(j(j+1)/2).
```

The cyclic recurrence is consistent because `nu^6 q^21=1`.  Entrywise,

```text
H (nu^(-1) Z X) H^(-1)=X.                              (H)
```

## Generator assignment

On `C^4 tensor C^6`, put

```text
x_alpha             = P_a tensor X,
x_beta              = P_b tensor I,
x_(alpha+beta)      = I,
x_(2alpha+beta)     = P_d tensor I,
x_(-alpha)          = A := P_k tensor H,
x_(-beta)           = B := nu I,
x_(-(alpha+beta))   = C := I tensor Z,
x_(-(2alpha+beta))  = D := A^(-1).
```

Relations (2.4), (2.5), and (2.6) follow respectively from `[a,b]=d`,
`d^2=1`, and `[X,Z]=qI=B^(-2)`.

For (2.12), `(P)` gives

```text
A (P_d tensor I) A^(-1)=P_(d b^(-1)) tensor I,
```

and hence

```text
[x_(2alpha+beta),x_(-alpha)]
 = (P_d tensor I) A (P_d tensor I) A^(-1)
 = P_(b^(-1)) tensor I
 = x_(alpha+beta)^(-1) x_beta^(-1).
```

For (2.7), put `T=nu I tensor Z^(-1)`.  Equation `(H)` and `ka=ak`
say precisely

```text
A (T^(-1) x_alpha) A^(-1)=x_alpha.
```

Rearranging gives `[x_alpha,A^(-1)]=T`, which is (2.7) because `D=A^(-1)`.
Finally `x_beta` commutes with `C`, while `AD=I`, proving (2.8).

The marked word remains

```text
w_beta=x_beta B^(-1)x_beta=nu^(-1)I,
w_beta^4=nu^(-4)I=omega I.                              (M)
```

Thus there is no representation-independent HS/Fox/SOS gap supported on
these six relations.

## Next sequential face

On this retuned packet Kassel (2.9) reads

```text
[x_(alpha+beta),x_(-alpha)] = x_(-beta)^(-2).
```

Its left side is `I`, while its right side is `qI`, so its normalized-HS
defect is exactly `|1-q|=1`.  This only identifies (2.9) as the next face
charging this packet; it does not yet prove that a further retuning cannot
also absorb (2.9).

