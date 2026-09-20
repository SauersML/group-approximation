# Concrete five-dimensional detector attack and the minimality obstruction

2026-09-20. The non-residually-finite hyperbolic-group target remains OPEN.
No finite detector was found and no persistent class was established.
This pass completely rules out one representation family over the entire
algebraic closure of characteristic 19, with explicit polynomial certificates.
It also identifies why the perfect-first-kernel argument does not close by
an elementary minimal-counterexample argument.

## 1. The constructive target

Use the pinned triangle of three copies of `S=PSL_2(F_19)`, with the
edge generators represented by

```
x12 = [[2,11],[16,3]],
x13 = [[5,11],[4,9]],
x23 = [[6,15],[12,8]].
```

The parallel wave-two work established hyperbolicity, perfectness of the
canonical first kernel, and a second independent simple quotient. Those
results motivate this attack but are not premises of the algebraic exclusion
proved below. In particular, no untracked wave-two node is needed to verify
the new theorem.

Let `rho=Sym^4` of the natural two-dimensional representation in
characteristic 19. Since `rho(-I)=I`, it is a representation of `S`.
It has dimension five and determinant one. Every order-five edge acts
with the five distinct fifth roots of unity as its eigenvalues. This
makes it a plausible small detector: the center of `SL_5(F_361)` has
order five, and multiplying an edge matrix by a primitive fifth root
preserves its conjugacy class. There is no individual-edge spectral
obstruction.

The following computation nevertheless proves that the three edges
cannot be fitted together with any nonzero central five-twist.

**Theorem.** Let `K` be any algebraically closed field of characteristic
19. For every nonzero twist `d=(d12,d13,d23) in F_5^3`, there is no
homomorphism from the centrally twisted triangle colimit to `GL_5(K)`
whose central generator has nontrivial scalar image and whose three
canonical `S`-vertex restrictions are conjugate to `rho`.

The same holds over every finite extension of `F_19`. The restrictions
on characteristic, dimension, and vertex representation are essential
parts of this statement. It does not classify all five-dimensional
representations or all finite detectors.

## 2. Reduction to a finite collection of exact polynomial identities

Put `k=F_19[z]/(z^2-4z+1)`. The polynomial is irreducible over `F_19`,
and `z` has order five. These assertions are also checked exactly by
the construction script. Set

```
A=rho(x12), B=rho(x13), C=rho(x23).
```

For explicit reproduction, in the basis `X^(4-i)Y^i`, `0<=i<=4`, the
column indexed by `i` of `rho([[a,b],[c,d]])` consists of coefficients
of `(aX+cY)^(4-i)(bX+dY)^i`. The script verifies determinant one,
fifth powers, invariance under the sign of each natural lift, and the
representation identity on all pairs of displayed edge matrices.

Fix the edge-twist convention
`s_i(x)=Z^(dij) s_j(x)` on an edge from `i` to `j`. After simultaneous
conjugation, a purported representation has vertex maps

```
rho,  U rho U^(-1),  V rho V^(-1).
```

If `Z` maps to `zI`, the edge equations are equivalent to

```
U A = z^a A U,
V B = z^b B V,
W C = z^c C W,
U=VW,
(a,b,c)=(-d12,-d13,d23).                         (1)
```

A different nontrivial scalar image of `Z` merely gives another nonzero
triple. All 124 triples are checked individually; there is no assumption
that multiplication by a nonzero element of `F_5` preserves this
representation family. In particular `z->z^2` is not an `F_19` field
automorphism, so reducing to 31 projective lines would not be justified.

Choose eigenbases `P_B,P_C` with eigenvalues ordered `1,z,...,z^4`.
Let `T_b` send the standard basis vector indexed by `j` to that indexed
by `j-b mod 5`. The complete set of solutions of the second equation
in (1) is

```
V=P_B T_b diag(v0,...,v4) P_B^(-1),
```

and similarly

```
W=P_C T_c diag(w0,...,w4) P_C^(-1).
```

These formulas follow entry by entry from the distinct eigenvalues;
no possible intertwiner is discarded. Invertibility is equivalent to
all ten diagonal coefficients being nonzero. Multiplying `V` and `W`
by independent scalar factors changes none of (1), since `U=VW` is
scaled accordingly. Hence normalize `v0=w0=1`.

There remain eight diagonal coefficients. Add a ninth variable `inv`
and the equation

```
inv * v1*v2*v3*v4*w1*w2*w3*w4 - 1 = 0.            (2)
```

For each nonzero `(a,b,c)`, let `f_1,...,f_25` be the entries of
`(VW)A-z^a A(VW)`, and let `f_26` be (2). These are polynomials over
`k` in nine variables. Equations (1) have an invertible solution over
an extension of `k` if and only if all 26 polynomials vanish there.
No finite-field equations such as `v_i^361-v_i` are imposed.

## 3. The completed certificate and its exact scope

For every one of the 124 nonzero triples, the supplied certificate
contains 26 polynomial multipliers satisfying

```
sum_(i=1)^26 h_i f_i = 1.                         (3)
```

The identities were obtained by Sage 10.7/libSingular and checked there
by direct polynomial multiplication. A separate pure-Python verifier
then checked every identity using sparse polynomials and the explicit
finite-field multiplication rule

```
(a+bz)(c+dz)=(ac-bd)+(ad+bc+4bd)z mod 19.
```

The hardened verifier binds those identities to the advertised problem.
Starting from the three pinned two-by-two matrices, it reconstructs
`Sym^4` by repeated polynomial multiplication, independently of the
generating script's binomial-coefficient formula. It matches `A,B,C`,
checks their fifth powers, inverts `P_B,P_C` by exact Gaussian
elimination, and checks both ordered eigenvalue identities. It then
reconstructs every shifted-diagonal `V,W`, all 3,224 conjugacy and
saturation equations, and compares them exactly to the serialized
certificate inputs before multiplying by the supplied coefficients.

It also checks that the triple list is exactly
`F_5^3 minus {(0,0,0)}`, with no repetition or omitted case. The
certificate bundle contains the edge matrices, eigenbases, each set
of input polynomials, and its multipliers. Neither input reconstruction
nor verification of (3) requires Sage or a Groebner-basis algorithm.
The independent standard-library verifier returned PASS for all
these checks in 3.11 seconds; the receipt is retained below.

Evaluating (3) at a common zero over any extension field would give
`0=1`. This proves the theorem over an algebraic closure, and therefore
over every finite field of characteristic 19. It is a full exhaustion
of this conjugate-`Sym^4` family, not a finite-field sampling assertion.

All computation ran on MSI `acn112`, nice level 19, CPU affinity to
one core. The complete 124-case pass finished in 11.60 seconds under
a 55-second outer wall cap and 52-second CPU cap. The original identity
verifier finished under a 15-second cap; its hardened replacement,
which also reconstructs and binds every input, finished in 3.11 seconds
under a 30-second wall cap and 28-second CPU cap. All storage and temporary
directories were under
`/projects/standard/hsiehph/sauer354/hrf-breakthrough-2026-09-20-sym4`.
No local computation ran, no packages were installed, and all processes
finished normally. An earlier all-case setup run exited before testing
any case because constant matrices were inverted after polynomial-ring
coercion; the corrected source inverts over `F_361` before coercion.
That failed setup is not counted as evidence.

Owned replay and evidence files in `research/artifacts/`:

- `hrf-breakthrough-2026-09-20-sym4.py`: matrix and one-case construction.
- `hrf-breakthrough-2026-09-20-all-twists.py`: exhaustive 124-triple pass.
- `hrf-breakthrough-2026-09-20-certificate.py`: initial one-case certificate.
- `hrf-breakthrough-2026-09-20-verify.py`: exact input/identity/coverage verifier;
  accepts the combined certificate JSON as an argument.
- `hrf-breakthrough-2026-09-20-certificates.json`: combined exact certificate.
- `hrf-breakthrough-2026-09-20-results.json`: per-case results.
- `hrf-breakthrough-2026-09-20-run.out`: complete successful run output.
- `hrf-breakthrough-2026-09-20-verify.out`: hardened independent verifier receipt.

For replay on MSI, place the first two construction scripts in the
specified project directory as `probe.py` and `all-twists.py`. Run the
latter with the installed `sagemath/10.7` module, task-local `TMPDIR`
and `DOT_SAGE`, one CPU, and the stated cap. To verify the combined
downloaded certificate, use ordinary Python with the verifier and
the certificate path; no Sage or Singular is needed for input reconstruction
or the identities.

## 4. Why perfect first kernels do not finish a minimal-detector induction

Suppose a nonzero central mark survives in some finite image. Choosing
a smallest image that still detects it makes every nontrivial normal
subgroup contain the mark: otherwise quotient that subgroup out.
This gives a unique minimal normal central `C_5`. It does not imply
that the image is quasisimple, or that its solvable radical is central.
The following completely explicit algebraic construction demonstrates
the obstruction with the same simple group `S=PSL_2(F_19)`.

Write `k0=F_5`, let `k0[S]` be the regular permutation module, let
`I` be its augmentation ideal, and let `n=sum_(s in S) e_s`.
Since `5` divides `|S|=3420`, one has `n in I`. Set

```
H=I/k0 n.
```

The coefficient dot product on `k0[S]` has `I=n^perp`, and the
radical of its restriction to `I` is exactly `k0 n`. It therefore
gives an invariant nondegenerate symmetric form on `H`.

The coinvariants `I_S` vanish. Indeed, writing `t_g` for the class of
`e_g-e_1` in `I_S`, the coinvariant relations give
`t_(gh)=t_g+t_h`. The `t_g` generate, and `S` is perfect, so all
are zero. Consequently `H_S=0`.

The action on `H` is faithful. Its kernel is normal in the nonabelian
simple group `S`. The action is not trivial: for `s` of order five
and `h` outside `<s>`, the vector
`(s-1)(e_h-e_1)=e_(sh)-e_s-e_h+e_1` has four distinct supported
coordinates and is not a multiple of `n`. Thus the kernel is trivial.

Let `V=H direct-sum H`, with its invariant nondegenerate alternating
form

```
b((u,v),(u',v')) = <u,v'> - <v,u'>.
```

Form the finite Heisenberg group `P=V x k0` with multiplication
`(v,t)(w,u)=(v+w,t+u+b(v,w)/2)`, and put `E=P semidirect S`.
Here `Z(P)=P'=k0`, and `S` acts trivially on this center. Since
`V_S=0` and `S` is perfect, `E/Z(P)` is perfect. Also
`Z(P)=P'<=E'`, so `E` itself is perfect.

Every nontrivial normal subgroup of `E` contains `Z(P)`. To see this,
let `L` be normal and suppose `L` meets `Z(P)` trivially. A nontrivial
normal subgroup of `P` must meet its center: a noncentral element has
a nontrivial commutator with `P`, by nondegeneracy of `b`. Thus
`L intersect P=1`. Now `[L,P]<=L intersect P`, so `L` centralizes
`P`. Faithfulness of `S` on `V` and nondegeneracy of `b` give
`C_E(P)=Z(P)`, whence `L=1`.

Thus `E` is perfect with a unique central minimal normal subgroup
of order five, yet it has the large noncentral solvable normal subgroup
`P`. Its only nonabelian simple composition factor is `PSL_2(F_19)`.

There is a second failure if one tries to retain the canonical quotient
during minimalization. Put `F=E x S` and mark `(Z(P),1)`. Projection
onto the second factor has perfect kernel `E`, exactly the coarse
finite-kernel property furnished by the perfect first kernel. Quotienting
by `1 x S` preserves the central mark and reaches the monolithic group
`E`, but destroys that specified quotient map to `S`. Minimality among
all detectors and minimality among refinements of the fixed canonical
map are different requirements; their conclusions cannot be combined.

This example is not claimed to be a quotient of the pinned triangle.
It proves precisely that the abstract perfect-kernel, composition-factor,
and minimality conditions alone do not eliminate the remaining detectors.
The actual three vertex maps and their edge relations must enter a
further argument. The `Sym^4` computation above does use those relations,
but only for the stated representation family.

## 5. Sources and remaining task

The extension and module facts in Section 4 have complete proofs above;
no classification of finite simple groups or unverified representation
table is used. The symmetric-power construction is explicit. The only
software-specific step consulted externally was Sage's official
[polynomial lift documentation](https://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/multi_polynomial_libsingular.html),
which specifies the coefficients returned by `1.lift(I)`; the resulting
identities were then independently checked by arithmetic. Literature and
repository searches found no recorded copy of this pinned-triangle
calculation. No claim of general mathematical novelty is made.

The current-status primary source retained from the same-day check is
[Cui--Wan, Section 1.2](https://arxiv.org/html/2604.04007), which states
the general hyperbolic residual-finiteness problem as open. No Liu or
Thom approximation theorem enters this finite-group computation.

Before finalizing, I read the concurrent wave-three detector artifact
`hyperbolic-rf-wave3-detectors-2026-09-20.md` and its associated
square-kernel retention claim. That work proves survival in the
specified `PSL_2(19)^2` cover using 400 permutation coordinates.
The present characteristic-19 `Sym^4` exclusion is different: its
potential images lie in a rank-four projective linear ambient group,
and its parametrization covers every extension field within the stated
vertex representation family. Neither statement implies the other.
The wave-three work correctly leaves the square kernel's full first
homology unresolved; this artifact does not assume it is perfect.

The remaining target is still a proof of invisibility in every finite
quotient, or a genuine central detector that refutes a specific twist.
Different characteristics, dimensions, vertex representation types,
and the noncentral radical case remain uncontrolled. Neither the
verified 124-case exclusion nor the perfect-kernel property closes
that universal quantifier.

**Independent review.** A sibling proof-only review returned PASS for
the polynomial reduction in Sections 1--3 and the Heisenberg/minimality
obstruction in Section 4. That review did not itself execute the
certificates. The integrating coordinator separately read the hardened
standard-library verifier and found its arithmetic and input-binding
code correct. The bounded MSI run of that verifier returned the full
input-bound PASS receipt in 3.11 seconds. These are written review and
exact computational checks, not Lean certification or a solution of
the general residual-finiteness problem.
