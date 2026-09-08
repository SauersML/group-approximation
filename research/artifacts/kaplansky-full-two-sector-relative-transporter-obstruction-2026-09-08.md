# The complete exterior-square operator and a relative-character obstruction

Date: 2026-09-08. Exact formulas and a proved whole-family obstruction.
No computation is used. These results do not construct a group-ring
split or settle Kaplansky's conjecture.

Use the chart, projectors, and binary boundary module from
[the first-field-coordinate kernel artifact](kaplansky-first-field-coordinate-transporter-kernel-2026-09-08.md).
Write `B_4=F_4⊗_(F_2)B`, and let `sigma` conjugate scalar coefficients
by `omega -> omega^2`, fixing the binary tail basis. For an `F_4`-linear
operator `R` put `R^sigma=sigma R sigma`, which is again `F_4` linear.

## 1. The full source and target, not just selected vectors

Retain the four natural-sector embeddings `u_+,v_+,u_-,v_-` and set

```
k_+(xi,eta)=(u_+(xi)+v_+(xi)) wedge u_+(eta),
k_-(xi,eta)=(u_-(xi)+v_-(xi)) wedge u_-(eta),
J_+(xi,eta)=P_0(v_+(xi) wedge u_+(eta)),
J_-(xi,eta)=P_0(v_-(xi) wedge u_-(eta)).
```

The maps `k_+,k_-` identify the **entire** exterior-square source as

```
im f_0 = (B_4 tensor B_4)_+ direct-sum (B_4 tensor B_4)_-.
```

Indeed the mixed plus/minus sector has trivial central character and
is killed by `f_0`. On either remaining sector, `k` is injective by
its cross-coordinate tensor component. For a finite-dimensional tail
space of dimension `m`, the source rank is
`m+2 binom(m,2)=m^2`, using the determinant and two-tail projector
formulas. Thus the injective `m^2`-dimensional image of `k` is the
whole source. Every exterior vector uses a finite-dimensional tail
space, proving the assertion without an infinite-dimensional rank
comparison.

Likewise the symmetric alternating maps `J_+,J_-` identify

```
im P_0 = (Lambda^2 B_4)_+ direct-sum (Lambda^2 B_4)_-.
```

For basis tails, the vectors `J(e_i,e_j)` with `i<j` are nonzero and
belong to distinct two-tail blocks. They are therefore independent;
their number equals the target rank `binom(m,2)` on every finite tail
space. This proves the full target identification.

## 2. Exact operator for two arbitrary binary coordinate changes

Let `g=diag(a,b)`, where `a,b` are arbitrary invertible binary-linear
operators on their respective field-coordinate spaces. Define

```
a u_+(eta)=u_+(A eta)+u_-(B eta),
b v_+(xi)=v_+(C xi)+v_-(D xi).
```

Because `a,b` are defined over `F_2`, their actions on the minus
sectors are their Frobenius conjugates:

```
a u_-(eta)=u_+(B^sigma eta)+u_-(A^sigma eta),
b v_-(xi)=v_+(D^sigma xi)+v_-(C^sigma xi).
```

Let `alt:B_4 tensor B_4 -> Lambda^2 B_4` send `xi⊗eta` to
`xi wedge eta`. Under the complete identifications from Section 1,
the operator `P_0[g]f_0` is exactly

```
Phi_g(X,Y) = (
  alt((C tensor A)X)+alt((D^sigma tensor B^sigma)Y),
  alt((D tensor B)X)+alt((C^sigma tensor A^sigma)Y)
).
```

Here `X,Y` are arbitrary finite tensors. The plus-source formula is
the earlier identity

```
P_0[g]k_+(xi,eta)
  =J_+(C xi,A eta)+J_-(D xi,B eta),
```

and the minus-source formula is its Frobenius conjugate. The
first-coordinate wedges vanish after `P_0`; all mixed-character
wedges have trivial central character and vanish as well.

Thus injectivity of `Phi_g` is exactly injectivity on the complete
exterior-square source. It would still be only a necessary condition
for a group-ring split. Passing this representation would not produce
an element `L` satisfying `L P_0[g]f_0=f_0`.

## 3. Relative-character theorem, invariant under a shared left change

Identify the two binary field-coordinate spaces and write

```
c=b^-1 a,
c u_+(eta)=u_+(R eta)+u_-(T eta).
```

The relative operator `c` is invertible. Its character blocks satisfy

```
A=C R+D^sigma T,
B=D R+C^sigma T.
```

**Theorem.** If either `R` or `T` has a nonzero kernel, then
`P_0[g]f_0` has a nonzero kernel in the complete exterior-square
source. In particular it has no left inverse on `f_0`, even with
unrestricted ambient group-algebra coefficients in that inverse.

First suppose `T eta=0` for nonzero `eta`. Invertibility of `c`
implies `xi=R eta!=0`. Then

```
A eta=C xi,       B eta=D xi,
```

so

```
P_0[g]k_+(xi,eta)
  =J_+(C xi,C xi)+J_-(D xi,D xi)=0.
```

The source vector is nonzero and fixed by `f_0`.

Next suppose `R eta=0` for nonzero `eta`. Set `tau=T eta`, which is
nonzero by invertibility. Use both source sectors:

```
w=k_+(sigma tau,eta)+k_-(tau,sigma eta).
```

The two summands are nonzero and belong to different nontrivial
central-character sectors. Hence they cannot cancel and `f_0w=w!=0`.
The first hypothesis gives `A eta=D^sigma tau`,
`B eta=C^sigma tau`; conjugation gives
`B^sigma(sigma eta)=C(sigma tau)` and
`A^sigma(sigma eta)=D(sigma tau)`. The full formula now yields

```
(P_0[g]w)_+
  =J_+(C sigma tau,D^sigma tau)
   +J_+(D^sigma tau,C sigma tau)=0,

(P_0[g]w)_-
  =J_-(D sigma tau,C^sigma tau)
   +J_-(C^sigma tau,D sigma tau)=0.
```

Symmetry of both `J` forms proves the cancellation. In fact this
`w` is fixed by `sigma`, so it is already a binary exterior vector.
In the first case, adding the Frobenius conjugate of the nonzero
plus-source vector also gives a nonzero binary source kernel.

The natural representation of `〈K,g〉` supplies the contradiction
to a proposed splitting identity. Conditional expectation onto its
subgroup algebra handles an inverse allowed in a larger ambient
group algebra, exactly as in the preceding artifacts.

The criterion depends only on `c=b^-1a`. Replacing `(a,b)` by
`(h a,h b)` for any shared invertible binary-linear operator `h`
does not change it. Thus a shared left change cannot repair a family
excluded by this relative test, however much that change mixes field
characters in the two individual blocks.

## 4. Relative linearity and semilinearity as special cases

If `c` preserves field characters, then `T=0` and `R` is bijective.
If it reverses them, then `R=0` and `T` is bijective. These are the
relative `F_4`-linear and `F_4`-semilinear cases, respectively; in
operator terms `c` normalizes the specified scalar field action.
Both are therefore excluded by Section 3.

The reversing case is not covered by the one-sector alternating
diagonal alone. Its proof uses the two-sector cancellation above;
omitting the second source sector would miss this whole-family
obstruction. The preserving case includes `a=b`, even when each
individual coordinate operator strongly mixes characters.

A possible split for a literal block-diagonal transporter must thus
have **both relative character blocks `R,T` injective**, in addition
to any other known requirements. This is a necessary condition only.
The theorem does not decide all relative operators with both blocks
injective, does not supply an actor passing the complete operator
`Phi_g`, and makes no claim for arbitrary chart coefficients inserted
around the transporter.
