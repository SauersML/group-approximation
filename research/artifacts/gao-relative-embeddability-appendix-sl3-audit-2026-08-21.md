# Gao Appendix Theorem 7.1 applied to the SL3 arithmetic inclusion

Date: 2026-08-21

Primary source: Weichen Gao, with appendix by Marius Junge and David Gao,
*Relative Embeddability of von Neumann Algebras and Amalgamated Free
Products*, arXiv:2012.07940v3, Appendix Theorem 7.1 and Lemmas 7.1--7.2:
<https://arxiv.org/html/2012.07940#S7>.

## Exact source statement

For finite von Neumann algebras `N subset M` and a finite FACTOR `N_1`, Gao
proves equivalence of:

1. `N subset M` is `RE/N_1`;
2. `(M tensor L^infinity(S^1)) *_N M` embeds trace-preservingly into
   `(R tensor N_1)^omega`.

If, in addition, there is a unitary `u in M` satisfying

```text
E_N(u^n)=0       for every nonzero integer n,                   (GA1)
```

these are also equivalent to:

3. the PLAIN double `M *_N M` embeds trace-preservingly into
   `(R tensor N_1)^omega`.

The factor hypothesis on `N_1` is used in Lemma 7.1 to put equal-trace
spectral projections into a matrix subalgebra of the target ultrapower.  The
unitary hypothesis `(GA1)` is used in the proof of `3=>1`: powers of `u` in
the first free component make the conditional expectation onto its
commutant vanish on `M minus N` in the second component.  Neither hypothesis
may be omitted when citing the theorem.

## The SL3 group-factor inclusion meets both hypotheses

Set

```text
C=SL_3(Z),   A=SL_3(Z[1/2]),   N=L(C),   M=L(A).
```

The group `C` is ICC with trivial center, so `N` is a II_1 factor.  It is CE
because `C` is residually finite.  Thus `N_1=N` is an allowed finite factor
and `R tensor N` is CE.

Let `h=diag(2,1,1/2)` and `u=lambda_A(h)`.  Every nonzero power `h^n` has a
nonintegral diagonal entry, so it lies outside `C`.  The group conditional
expectation kills precisely Fourier coefficients outside `C`, giving
`E_N(u^n)=0` for every `n!=0`.  This is exactly `(GA1)`.

Therefore

```text
L(A) *_L(C) L(A) is CE
    <=> L(C) subset L(A) is RE/L(C).                           (GA2)
```

The forward direction uses the canonical embedding `R^omega ->
(R tensor L(C))^omega`, `x |-> x tensor 1`.  The reverse direction uses
Gao's theorem and CE of `R tensor L(C)`.

Finally, the tracial group-factor identity

```text
L(A *_C A)=L(A) *_L(C) L(A)
```

turns `(GA2)` into the group statement: the plain arithmetic double is
hyperlinear iff the inclusion is `RE/L(C)`.

## Correction to the previous Cairn boundary

The enlarged amalgam

```text
(L(A) tensor L(Z)) *_L(C) L(A)
```

is the unconditional converse object in Gao's theorem.  Previous Cairn text
correctly used that object but left open whether the appendix's extra
hypothesis applies to the plain double.  It does apply in rank three, via
the dyadic diagonal `h`.  Hence no `L(Z)` enlargement is needed for the SL3
inclusion.

This does not prove non-relative-embeddability.  It identifies the precise
remaining statement and proves it is equivalent, not merely related, to the
plain-double hyperlinearity problem.
