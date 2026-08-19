# The direct-double relative-embeddability converse needs a commuting unitary

Date: 2026-08-12

## 1. Correction

The notebook previously asserted

```text
L(G *_Gamma G) is CE
  iff L(Gamma)<L(G) is RE/C.                            (REG1)
```

The forward implication was attributed to the implication `(3)=>(1)` in
Theorem 7.1 of Gao--Junge--Gao, *Relative Embeddability of von Neumann
Algebras and Amalgamated Free Products*, arXiv:2012.07940v3.  The proposed
application chose a group unitary `u=lambda(a)` with

```text
E_L(Gamma)(u^n)=0,       n!=0,                         (REG2)
```

but `a` does not commute with `Gamma`.

This does not establish `(REG1)`.  The Appendix proof constructs the square

```text
hat M                 contains M
  contains                 contains
<u>' intersect hat M contains N,                       (REG3)
```

where `N=L(Gamma)` and `M=L(G)`.  For the lower horizontal inclusion in
`(REG3)` even to exist, one needs

```text
u in N' intersect hat M.                               (REG4)
```

Condition `(REG2)` does not imply `(REG4)`.  In the group application it
explicitly fails whenever `a` fails to centralize `Gamma`.

The point here is a gap in this use of the converse, not a claimed
counterexample to the conclusion of Gao--Junge--Gao's stated theorem.  Their
printed proof verifies that the conditional expectation from the second
free factor onto `<u>' intersect hat M` kills `M minus N`; it does not verify
the prerequisite containment `N subset <u>'`.  The proof works with the
additional hypothesis `(REG4)`, and it also works for their alternative
enlarged algebra because the circle-coordinate Haar unitary commutes with
`N`.

Accordingly, the reverse implication in `(REG1)` is presently unsupported
and must not be used as a theorem in this project.

## 2. Exact audit of the proof

Let

```text
hat M=M *_N M,                                         (REG5)
```

with `M` embedded as the second factor, and choose `u` in the first factor.
The Appendix averages

```text
A(x)=strong-lim_(m->infinity)
       (1/m) sum_(j=0)^(m-1) u^j x u^(-j).             (REG6)
```

For `x in M` with `E_N(x)=0`, amalgamated freeness and `(REG2)` do imply

```text
A(x)=0.                                                (REG7)
```

But for `n in N`, the amalgamation identifies its two copies, and

```text
u n u^*=n    iff    [u,n]=0.                           (REG8)
```

Thus `(REG7)` proves the desired expectation identity only after `(REG8)`
has made `N` a subalgebra of the fixed-point/commutant algebra.  Without
`(REG8)`, `(REG3)` is not a square of inclusions.

In the Kun--Thom application, taking an infinite-order element in the
`SL_d(Z)` coordinate gives `(REG2)` because its nonzero powers lie outside
`Gamma`, but conjugation by that element acts nontrivially on `Gamma`.
Hence `(REG8)` fails.

## 3. Correct surviving statements

The forward relative-embeddability theorem remains applicable:

```text
L(Gamma)<L(G) is RE/C
  implies L(G *_Gamma G) is CE.                        (REG9)
```

Also, Gao--Junge--Gao's enlarged converse gives

```text
(L(G) tensor L_infinity(S^1)) *_L(Gamma) L(G) is CE
  implies L(Gamma)<L(G) is RE/C,                       (REG10)
```

because the circle Haar unitary commutes with the amalgam and has vanishing
nonzero moments.

Neither `(REG9)` nor `(REG10)` turns CE of the un-enlarged direct double
into relative embeddability.  The precise current implications are

```text
RE/C  =>  direct double CE,
enlarged double CE  =>  RE/C,                          (REG11)
```

with no justified reverse arrow from the ordinary direct double.

## 4. Consequence for the one-vertex target

The new edge unitary `v` cannot repair this converse application.  It
normalizes the common edge by

```text
v x v^*=alpha(x),       x in P,                        (REG12)
```

rather than commuting with it.  Moreover `v^2=1`, so it is not a relative
Haar unitary: its even powers lie in `P`.  Therefore neither `(REG4)` nor
`(REG2)` holds for `v` relative to `P`.

The exact group-corner identity in
`FALSE_ONE_VERTEX_GROUP_CORNER_AND_COVER.md` remains valid and is independent
of relative embeddability.  What this audit removes is only an unjustified
claim that the remaining CE gate is already equivalent to a known RE/C
condition.

## Source checked

W. Gao, M. Junge, and W. Gao, *Relative Embeddability of von Neumann
Algebras and Amalgamated Free Products*, arXiv:2012.07940v3, especially
Theorem 7.1 and the proof of `(2)=>(1)` and `(3)=>(1)` in the Appendix:
<https://arxiv.org/abs/2012.07940>.
