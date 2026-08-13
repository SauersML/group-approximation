# A coset-tower Bernoulli core gives an exact nonamenable wall

Date: 2026-08-12

## 1. Outcome

Let \(\Gamma\) be countable and let

\[
 \beta:\Gamma\longrightarrow\Gamma
 \tag{CTD1}
\]

be an injective endomorphism.  Fix

\[
 \gamma\in\Gamma\setminus\beta(\Gamma).
 \tag{CTD2}
\]

There is a canonical generalized Bernoulli crossed product \(N\), a
trace-preserving proper endomorphism \(\alpha:N\to N\) extending \(\beta\),
and a unitary

\[
 a\in \alpha(N)'\cap N
 \quad\text{with}\quad [a,u_\gamma]\neq0.
 \tag{CTD3}
\]

Passing to the automorphic dilation of \(\alpha\) converts `(CTD3)` into the
exact relative-commutant wall

\[
 v\in\pi(\Gamma)'\cap M,
 \qquad [v,\pi(t^{-1}\gamma t)]\neq0
 \tag{CTD4}
\]

for the ascending HNN group

\[
 P=\langle\Gamma,t\mid t\delta t^{-1}=\beta(\delta),\ \delta\in\Gamma\rangle.
 \tag{CTD5}
\]

Moreover, if \(N\) is Connes embeddable, then so is the dilation algebra
\(M\).  Thus the local compressor wall is not merely heuristic: all group
relations, the finite trace, and the marked commutator are exact.  The only
analytic hypothesis left is Connes embeddability of one explicit
nonamenable generalized Bernoulli crossed product.

For the framed Kun--Thom compressor, `(CTD5)` is only the ascending
one-compressor subsystem of the full infranormal vertex.  The current
complete-radical theorem is stated for the full infranormal pair, so this
note does **not** yet prove that the marked word is in the sofic radical of
the smaller double.  This scope issue is load bearing and prevents the
construction below from being advertised as a solution.

## 2. The coset tower

For \(n\geq1\), put

\[
 X_n=\Gamma/\beta^n(\Gamma),
 \qquad X=\bigsqcup_{n\geq1}X_n.
 \tag{CTD6}
\]

Define

\[
 F_n(g\beta^n(\Gamma))
   =\beta(g)\beta^{n+1}(\Gamma).
 \tag{CTD7}
\]

Injectivity of \(\beta\) makes `(CTD7)` a well-defined injection.  Their
disjoint union \(F:X\to X\) satisfies

\[
 F(\delta x)=\beta(\delta)F(x)
 \qquad(\delta\in\Gamma,x\in X).
 \tag{CTD8}
\]

Let

\[
 A=\overline\bigotimes_X(\mathbf C^2,\tau_0)
 \tag{CTD9}
\]

with the Bernoulli action of \(\Gamma\), and put

\[
 N=A\rtimes\Gamma.
 \tag{CTD10}
\]

Map the tensor factor at \(x\) identically to the tensor factor at \(F(x)\)
and put the identity on the unused factors.  This defines a normal unital
trace-preserving embedding

\[
 \alpha_A:A\longrightarrow A.
 \tag{CTD11}
\]

Equation `(CTD8)` is exactly the covariance identity

\[
 \alpha_A(\delta\cdot b)=\beta(\delta)\cdot\alpha_A(b).
 \tag{CTD12}
\]

Consequently

\[
 \alpha(b)=\alpha_A(b),
 \qquad \alpha(u_\delta)=u_{\beta(\delta)}
 \tag{CTD13}
\]

extends to a normal unital injective trace-preserving endomorphism of
`(CTD10)`.

## 3. The exact relative commutant inside the core

Let

\[
 x_0=\beta(\Gamma)\in X_1.
 \tag{CTD14}
\]

The subgroup \(\beta(\Gamma)\) fixes \(x_0\).  Let \(z\in\mathbf C^2\) be
the mean-zero self-adjoint unitary and let \(a=z_{x_0}\in A\) be its copy at
the root coordinate.  Since \(A\) is abelian, \(a\) commutes with
\(\alpha_A(A)\), and root invariance gives

\[
 [a,u_{\beta(\delta)}]=0
 \qquad(\delta\in\Gamma).
 \tag{CTD15}
\]

Equations `(CTD13)--(CTD15)` prove

\[
 a\in\alpha(N)'\cap N.
 \tag{CTD16}
\]

On the other hand, `(CTD2)` says that \(\gamma x_0\neq x_0\).  Distinct
Bernoulli coordinates are independent, and hence

\[
 \|[a,u_\gamma]\|_2^2
  =\|a-\gamma\cdot a\|_2^2=2.
 \tag{CTD17}
\]

This is the nonamenable-core phenomenon excluded from the amenable no-go in
`FALSE_AMENABLE_RELATIVE_CORE_NO_GO.md`.

## 4. Automorphic dilation

Let \((\widetilde N,\widetilde\alpha)\) be the minimal automorphic dilation
of \((N,\alpha)\).  Thus \(N\subseteq\widetilde N\),
\(\widetilde\alpha|_N=\alpha\), and

\[
 \widetilde N=\overline{\bigcup_{m\geq0}
                 \widetilde\alpha^{-m}(N)}^{\,\mathrm{SOT}}.
 \tag{CTD18}
\]

Form

\[
 M=\widetilde N\rtimes_{\widetilde\alpha}\mathbf Z
 \tag{CTD19}
\]

and choose the implementing unitary \(U\) with

\[
 UxU^*=\widetilde\alpha(x).
 \tag{CTD20}
\]

Define a representation of `(CTD5)` by

\[
 \pi(\delta)=u_\delta\in N,
 \qquad \pi(t)=U.
 \tag{CTD21}
\]

Put

\[
 v=U^*aU.
 \tag{CTD22}
\]

For every \(\delta\in\Gamma\), conjugating the desired commutator by \(U\)
and using `(CTD16)` gives

\[
 U[v,u_\delta]U^*=[a,u_{\beta(\delta)}]=0.
 \tag{CTD23}
\]

Thus \(v\in\pi(\Gamma)'\cap M\).  If

\[
 h=t^{-1}\gamma t,
 \tag{CTD24}
\]

then

\[
 U[v,\pi(h)]U^*=[a,u_\gamma],
 \tag{CTD25}
\]

so `(CTD17)` gives the dimension-free exact value

\[
 \|[v,\pi(h)]\|_2^2=2.
 \tag{CTD26}
\]

This proves `(CTD4)`.

## 5. Connes-embeddability reduction

Connes embeddability is stable under trace-preserving inductive limits.
It is also stable under crossed products by amenable discrete groups.
Therefore

\[
 N\text{ Connes embeddable}
 \quad\Longrightarrow\quad
 \widetilde N\text{ Connes embeddable}
 \quad\Longrightarrow\quad
 M\text{ Connes embeddable}.
 \tag{CTD27}
\]

The hypothesis in `(CTD27)` has a concrete group form.  The algebra
`(CTD10)` is the group von Neumann algebra of

\[
 W=\Bigl(\bigoplus_X C_2\Bigr)\rtimes\Gamma.
 \tag{CTD28}
\]

Thus the remaining local analytic question is precisely whether the
generalized wreath product `(CTD28)` is hyperlinear.  Its point stabilizers
are the nonamenable Kazhdan groups \(\beta^n(\Gamma)\), so neither the
amenable-stabilizer theorem nor the standard sofic-action wreath-product
theorem applies.  Conversely, a direct finite-rank compression of the
coset representation is blocked by the Kazhdan trace-gap argument.

This is nevertheless a sharper target than a free matrix search: prove
Connes embeddability of one explicit Bernoulli crossed product, and the
complete relative wall follows automatically from `(CTD18)--(CTD26)`.

## 6. Interface with the full Kun--Thom endpoint

For a strict compressor \(t\) in the framed pair, take

\[
 \beta(\delta)=t\delta t^{-1}.
 \tag{CTD29}
\]

The strict predecessor relation

\[
 h=t^{-1}\gamma t\notin\Gamma
 \tag{CTD30}
\]

is exactly `(CTD2)`.  Hence all operator-algebraic parts of the wall are
already solved by the tower.

What is not automatic is the sofic-radical input.  Kun--Thom's complete
radical theorem uses the full inclusion \(\Gamma<G\) and the fact that the
entire compressor semigroup generates \(G\).  The subgroup `(CTD5)` need
not inherit infranormality.  Accordingly, one still needs one of the
following genuinely new statements:

1. the marked word for the double of `(CTD5)` is itself in the sofic
   radical;
2. the tower representation extends from `(CTD5)` to the full framed
   vertex \(G\) while preserving `(CTD26)`; or
3. the group `(CTD28)`, or its automorphic dilation, is independently
   proved nonsofic.

Without one of these bridges, `(CTD27)` is a rigorous local CE reduction,
not yet a hyperlinear-nonsofic group.

## 7. The one-edge Clifford upgrade is Connes embeddable

The central-commutator formulation in
`EXPLICIT_FINITELY_PRESENTED_NON_MF_GROUP.md` needs only one
anticommuting orbital edge, rather than the complete Clifford algebra on
`G/Gamma`.  For the finite-index tower this stronger local wall can be
constructed without any remaining CE hypothesis.

Assume in this section that every `X_n=Gamma/beta^n(Gamma)` is finite and
retain `X` and the injection `F` from `(CTD6)--(CTD8)`.  Let

```text
A_Cl=Cl_R(ell2(X))
```

be the tracial CAR/Clifford algebra with self-adjoint Majoranas `C_x`,
`x in X`.  Thus

```text
C_x^2=1,
C_x C_y=-C_y C_x             (x!=y).
```

The permutation action of `Gamma` on `X` gives trace-preserving Bogoliubov
automorphisms.  The injection `F` gives a trace-preserving unital embedding

```text
alpha_A(C_x)=C_(F(x)).                                (CTD31)
```

Equation `(CTD8)` is precisely the covariance needed to extend `(CTD31)`
to an endomorphism of

```text
N_Cl=A_Cl crossed_product Gamma,
alpha(u_delta)=u_(beta(delta)).                       (CTD32)
```

Unlike the generalized CAR action on the full infinite coset space, the
crossed product in `(CTD32)` is Connes embeddable for a direct finite-stage
reason.  The union of the first `m` tower levels is a finite
`Gamma`-invariant set.  Its Clifford algebra is finite dimensional, and
the action on it factors through the finite permutation action on those
levels.  The kernel is a finite-index subgroup of the residually finite
group `Gamma`, hence has a Connes-embeddable group algebra.  Crossing the
finite-dimensional Clifford algebra by the finite quotient preserves CE.
The algebras from the finite level unions increase trace preservingly to
`N_Cl`, so inductive-limit permanence gives

```text
N_Cl is Connes embeddable.                            (CTD33)
```

Take the automorphic dilation and crossed product by `Z` exactly as in
`(CTD18)--(CTD21)`.  Put

```text
x_0=beta(Gamma) in X_1,
a_0=C_(x_0),
C=U^* a_0 U.
```

The point `x_0` is fixed by `beta(Gamma)`, so the calculation in `(CTD23)`
gives

```text
C in pi(Gamma)'.                                     (CTD34)
```

For `gamma in Gamma-beta(Gamma)` and
`h=t^(-1) gamma t`, conjugation by `U` identifies `C` and `pi(h)Cpi(h)^*`
with the two distinct Majoranas `C_(x_0)` and `C_(gamma x_0)`.  Hence

```text
C pi(h)Cpi(h)^*=-pi(h)Cpi(h)^* C,                    (CTD35)
[C,pi(h)Cpi(h)^*]=-1.
```

The dilation algebra is CE by `(CTD33)` and the permanence argument in
`(CTD27)`.  Therefore `(CTD34)--(CTD35)` solve the complete one-edge
Connes-embeddable character problem for the ascending HNN subsystem.

This still does not finish FALSE.  The Kun--Thom full-sofic-radical theorem
requires the full infranormal Kazhdan vertex `G`; the ascending HNN group
maps onto `Z` and is not Kazhdan.  The remaining bridge is now purely the
extension problem: extend this one-edge CE representation from the HNN
subsystem to the full vertex while preserving `(CTD35)`, or prove an
independent radical theorem for a group carrying the same local dilation.
