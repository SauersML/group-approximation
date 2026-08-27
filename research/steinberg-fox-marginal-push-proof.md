---
rg: 2
id: steinberg-fox-marginal-push-proof
kind: route
title: Sum the rational chord actions over point and plane fibers
target: steinberg-fox-marginal-pushes-are-explicit
requires:
  - steinberg-tree-cuts-are-five-marginals
  - steinberg-fox-chord-actions-are-explicit
---

Write `eta=1/2`.  Direct substitution in `(SCA2)`, with `(STM2)` on the
missing fiber, gives

```text
P_(L_q f)(a,b)=P(a+eta,b),       H_(L_q f)(c,d)=H(c,d+c/2),
P_(L_s f)(a,b)=P(a,b+a/2),      H_(L_s f)(c,d)=H(c+eta,d).
                                                               (SMP1)
```

The `h^(-1)` push scales `(a,b;c,d)` by `(1/2,1/4;1/2,1/4)`.
For the remaining one-denominator maps one obtains

```text
P_(L_A f)(a,b)=P(a/(1-2a),b/(1-2a))       if a!=eta,
               -C(2b)                     if a=eta,
H_(L_A f)(c,d)=-f(-eta,-c/2,c-2d),

P_(L_B f)(a,b)=-f(4(a-b),2b,-eta),
H_(L_B f)(c,d)=H(c/[2(1-c)],2d/(1-c))     if c!=1,
               -A(4d)                     if c=1,

P_(L_r f)(a,b)=-f(a+b,b,1),
H_(L_r f)(c,d)=H(c/(1+c),d/(1+c))         if c!=-1,
               -A(-d)                     if c=-1.             (SMP2)
```

Their total sums are respectively `-A(-eta)`, `-C(-eta)`, and `-C(1)`.
Thus the only apparently non-fiber-preserving term left is `u`.  Put
`g=(1-q)f`.  Then

```text
P_g=P-P_q,       H_g=H-H_q,       C_g=T_g=0.          (SMP3)
```

For `b!=1`, set

```text
a'=(a+b/2)/(1-b),       b'=b/(1-b).
```

Then

```text
P_(L_u g)(a,b)= -g(a',b',1/(a+eta))        if a!=-eta,
                 P_g(-eta,b')              if a=-eta.           (SMP4)
```

On `b=1`, with `a!=-eta`, put `t=1/(a+eta)` and
`d_0=a/(a+eta)`; the value is `H_g(t,d_0)`.  At `(-eta,1)` it is
`-A_g(-eta)`.

For the plane push put `E=1+d+c/2`; when `c!=0` put
`a_*=-(2+c)/(2c)`.  If `E!=0`, set `c'=c/E`, `d'=d/E`.  The four cases are

```text
H_(L_u g)(c,d)= -g(a_*,a_*c'-d',c')       if E!=0 and c!=0,
                  H_g(0,d/(1+d))=0         if E!=0 and c=0,
                  P_g(a_*,-1)              if E=0 and c!=0,
                  0                         if (c,d)=(0,-1).       (SMP5)
```

Every exceptional value in `(SMP2)`, `(SMP4)`, and `(SMP5)` is exactly the
corresponding value from `(STM2)`.  Applying these formulas term by term to
`Xf=0` and `Yf=0` proves that both pushed rows are closed pointwise systems
in `f,P,H,A,C,T`, with no residual pushforward operator.
