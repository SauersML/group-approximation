# Compiler square defects, matrix reversal, and the spectral boundary

2026-09-08. Written group identities and finite-dimensional spectral
calculations. No script, search, build, or new Lean verification is used.
The normal-closure question for `p_1^2` is left unresolved.

## 1. The actual shared words

Let `C,B_1,B_2,B_3` be unitaries satisfying the marked factor laws

```text
C^3=I,       B_i^2=I,       [B_i,B_j]=I.
```

Use `[X,Y]=XYX^(-1)Y^(-1)` and the current
[eight-word compiler](leavitt-eight-word-exact-reduction-2026-09-08.md):

```text
gamma(X)=C X C^(-1),
d=[B_2,gamma(B_1)],       h=gamma^2(d),
a=[d,h],                 e=gamma(d),
u=[B_2,gamma(B_3)],       w=[gamma^2(B_1),a],
p_0=gamma(B_2),          q_0=w,
P=p_1=[e,u],             Q=q_1=[gamma^2(B_3),B_1],
X_0=p_0 q_0 p_0,         B=X_0 P Q P.                (1)
```

Here `B` is the compiled Thompson word, distinct from each marked
generator `B_i`. Also `gamma^2(X)=C^(-1)XC` by the cube relation.
No relation `P^2=I` or vanishing of the eight packet rows is assumed.

## 2. Exactly what the square anchor supplies

Put `x=B_2`, `y=gamma(B_1)`. Since both are involutions,

```text
d=xyxy,      x d x=y d y=d^(-1),
[x,d]=[y,d]=d^(-2).                                 (2)
```

Thus for every unitarily invariant norm,

```text
||[B_2,d]-I||=||[gamma(B_1),d]-I||=||d^2-I||.       (3)
```

Cyclic conjugation gives the same equality for the centralization of
`e` by `gamma(B_2),gamma^2(B_1)`, and of `h` by
`gamma^2(B_2),B_1`. In particular all six centralizations are exact
when `d^2=I`.

For another useful rewrite, put `E=e`, `U=u`, and `F=U E U^(-1)`.
Then `P=E F^(-1)`. If `d^2=I`, both `E` and `F` are involutions,
so

```text
P^2=[E,F]=[E,U E U^(-1)].                            (4)
```

This identifies a precise missing commutation: the square follows
if `E` commutes with this particular `U`-conjugate of itself.
For approximate square anchors, put `epsilon=||d^2-I||`. Since
`E` is conjugate to `d` and `F` to `E`,

```text
||E-E^(-1)||=||F-F^(-1)||=epsilon,
||P^2-[E,F]||<=2 epsilon.                            (5)
```

Indeed compare `P^2=E F^(-1) E F^(-1)` with
`[E,F]=E F E^(-1) F^(-1)` by changing the two indicated
inverse occurrences. Every other factor is unitary.

There is also an exact identity without a square assumption:

```text
E P E^(-1) P=[E^2,U].                               (6)
```

Expanding the left side cancels it to `E^2 U E^(-2) U^(-1)`.
Hence

```text
||E P E^(-1)-P^(-1)||<=2 epsilon.                   (7)
```

At `epsilon=0`, (7) gives reversibility of `P`, not its square
relation. For example, if `E=diag(1,-1)` and `U` is the real
plane rotation through `pi/6`, then `EUE=U^(-1)` and
`P=[E,U]=U^(-2)`, whose square is not identity. This example
only distinguishes these local statements; it is not a model of
the full compiler or `T_8`.

## 3. A shared-word matrix reversal estimate

Let

```text
Z'=C^(-1) B_3 C,       Y=B_1,
R=X_0^(-1) B=PQP,     S=PQP^(-1),
J=P Y P^(-1),         K=P Z' P^(-1).                (8)
```

Both `Y,Z'` are involutions by the marked factor laws. Thus

```text
Q=[Z',Y]=(Z'Y)^2,       Y Q Y=Q^(-1),
J^2=K^2=I,             S=[K,J]=(KJ)^2,
J S J=S^(-1).                                       (9)
```

These involutions are prescribed shared words, not freely selected
matrices. If the marked second factor has its regular-multiple
profile, each of `B_1,B_3` has trace zero, and therefore so do
the particular `J,K` in (8).

Write `delta=||P^2-I||`. Unitary invariance gives the exact equality

```text
||R-S||=||P Q(P-P^(-1))||=||P^2-I||=delta.          (10)
```

Using (9), the triangle inequality and invariance of the norm under
unitary multiplication yield

```text
||J R J-R^(-1)||
 <=||R-S||+||S^(-1)-R^(-1)||
 =2 delta.                                          (11)
```

Equations (3), (5), (7), and (10)--(11) hold for any unitarily
invariant norm with the triangle inequality, including every normalized
Schatten norm for `1<=p<=infinity`.

For normalized Hilbert--Schmidt norm and normalized trace, (9) implies
`tr(S^m)=tr(S^(-m))=conjugate(tr(S^m))`. Telescoping powers in
(10) consequently gives, for each integer `m>=1`,

```text
|Im tr(R^m)|<=|tr(R^m-S^m)|<=||R^m-S^m||_2
             <=m ||P^2-I||_2.                       (12)
```

Equivalently, the distance of the actual word `R` to the set of
commutators of two involutions is at most `delta`, with `S` an
explicit witness. This does not yet bound `delta` by the defect of
the eight imposed packet rows.

## 4. Exact finite-unitary characterization

**Lemma.** A unitary matrix `T in U(n)` is a commutator of two
involutions if and only if:

1. its eigenvalue multiset is invariant under complex conjugation;
2. its eigenvalue `-1` has even multiplicity.

When `n` is even, the two involutions may both be chosen to have
trace zero, equivalently equal positive and negative multiplicities.

For necessity, write `T=[H,J]` with `H^2=J^2=I`. Then
`J T J=T^(-1)`, giving the eigenvalue symmetry. Also `det T=1`.
Each nonreal conjugate eigenvalue pair has product one, so
`det T=(-1)^q`, where `q` is the `-1` multiplicity. Thus `q`
is even.

For sufficiency, diagonalize `T`. Match each nonreal eigenvalue
`lambda` with its conjugate, and pair the `-1` eigenvalues among
themselves. Each resulting block is `diag(lambda,conjugate(lambda))`,
where `lambda=-1` is allowed. Choose a unit scalar `zeta` with
`zeta^2=lambda`, and on that block put

```text
J = [ 0  1 ],        H = [ 0                zeta ],
    [ 1  0 ]            [ conjugate(zeta)   0    ].
```

Both are self-adjoint involutions of trace zero. Their product and
commutator are

```text
HJ=diag(zeta,conjugate(zeta)),
[H,J]=(HJ)^2=diag(lambda,conjugate(lambda)).          (13)
```

On the remaining `+1` eigenspace, set `H=J=I` to finish the
general construction. If `n` is even, the dimension of that remaining
space is even: all the previously treated blocks have dimension two.
Instead choose `H=J` there with half its eigenvalues `+1` and half
`-1`. Their commutator is still identity, and both total traces are
now zero. Conjugating back to the original basis proves the lemma.

The symmetry condition can also be stated as unitary conjugacy of
`T` and `T^(-1)`. Every finite-dimensional unitary has some unitary
square root; the lemma identifies the extra requirements for a square
of a product of two involutions.

## 5. Which part of the Thompson obstruction survives

For the actual source word (8),

```text
det P=det Q=1,       det R=det(PQP)=1                (14)
```

identically, since `P,Q` are commutators. Consequently the parity
condition in Section 4 is automatic as soon as the spectrum of `R`
has conjugation symmetry. In even dimension the lemma can then
reconstruct two trace-zero involutions realizing `R` as their
commutator.

Those reconstructed matrices need not equal the particular `J,K`
in (8). They need not extend to the marked `C_2^3`, be related by
the same cycle `C`, or satisfy any other compiler word. The lemma
therefore describes the limitations of unrestricted spectral tests,
not a model of the packet.

The
[seven-cell obstruction](leavitt-seven-cell-centralizer-completion-2026-09-08.md#6-nonreversibility-forces-a-noninvolutive-compiled-p1)
uses finite-prefix conjugation to preserve eventual-tail classes as
well as fixed-germ exponents. Its second obstruction counts possible
square-root orbits separately within those classes. These extra
constraints do not enter the finite-unitary characterization above.
The actual matrix conclusion supplied here is the quantitative
shared-word estimate (11)--(12). No additional dimension-uniform
spectral gap follows from the square and reversal properties alone.

## 6. The remaining derivability question

The
[native certificate, equation (5)](leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md#2-authenticate-the-compiler-in-the-native-leavitt-group)
identifies `p_1=x_23(t_1)` in the Leavitt group, so `p_1^2` is a
true native kernel word. Its unreduced length is `72`, twice the
unreduced length `36` of `p_1`.

The calculations here do not decide whether

```text
p_1^2 belongs to <<T_8>> inside C_3*C_2^3.           (15)
```

In particular the local example after (7) does not prove independence
from the full eight-row packet. Conversely, the existing exact
finite-dimensional certificate kills `C` in every exact matrix model
of `T_8`, and then makes `p_1=I`. That statement about exact matrix
models is not an abstract normal-closure proof of (15), and supplies
no bound uniform in matrix dimension for approximate models.

No derivation or independence claim for (15), no dimension-uniform
eight-row bound on `||P^2-I||_2`, and no nonhyperlinearity conclusion
is asserted.
