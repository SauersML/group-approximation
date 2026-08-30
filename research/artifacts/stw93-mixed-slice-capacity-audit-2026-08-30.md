# XCIII: mixed Jiang--Su slice capacity audit

## The direct cloning mechanism

The canonical central copy of `Z` contains, for every finite `n`, orthogonal
positive contractions `f_1,...,f_n` which are uniformly tracially large in
the property-(SI) sense.  Choose disjoint continuous plateau functions of a
full-spectrum positive element.  Faithfulness of the unique trace gives a
positive lower bound on every power of each plateau function.

If property (SI) could be applied with an arbitrary source `e` in the XCIII
trace-kernel ideal and each of these fixed-slice targets, the witnesses
would put `n` orthogonal Cuntz copies of `e` below the unit.  Since `n` is
arbitrary, every kernel cut would have infinite central Cuntz capacity.  The
finite-capacity obstruction then rules out every extra ordinary trace.

This target-restricted mixed-source statement is strictly less than full
property (SI): the large element is required to lie in one fixed central
Jiang--Su copy.  It is nevertheless stronger than the established
same-slice theorem, whose source also lies in that copy.

## Why the source distinction cannot be erased formally

In the doubled model

```text
D_0=F(Z) direct_sum F(Z),       I_0=J direct_sum F(Z),
delta(x)=(x,x),                 p=(0,1),
```

all same-slice property-(SI) tests have diagonal witnesses.  The model is
pure, its diagonal slice exhausts the hyperfinite factor quotient, and it
retains all of the previously isolated abstract slice data.  But the second
coordinate trace proves `cap_(D_0)(p)=1`; every nonzero spectral cut of `p`
has the same capacity.

Thus Jiang--Su target abundance and property (SI) internal to the slice do
not clone a source outside the slice.  A positive proof must use an
XCIII-specific mechanism to solve the mixed equation

```text
s*s=e,                 fs=s
```

for arbitrary `e in I_+` and fixed-slice large `f`.  Full-factor spectral
gap currently identifies the tracial quotient and makes the Jiang--Su slice
surjective there, but this is a `2`-norm statement; it does not by itself
produce the norm-level partial isometry `s`.

## Trust boundary

The doubled model is not an actual central sequence algebra and does not
contain the faithfully traced free-factor diagonal.  It only rules out a
formal implication from same-slice property (SI), pureness, and established
slice/quotient structure.  The mixed-source lemma is a conditional reduction,
not a proof of XCIII or of quasitrace linearity.
