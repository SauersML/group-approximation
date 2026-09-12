# The operator-MF passage in the hyperbolic equivalence: proof audit

Checked 2026-09-11. The implication from a hyperbolic group without residual
finiteness to a hyperbolic group without operator-MF approximation is **not
established by the existing citation route**. Its missing step is a passage
from norm matrix approximations to completely positive approximations. This
audit does not refute that implication or provide a counterexample to it.

## 1. Primary-source pinpoints

[Dadarlat, arXiv:2007.12655v2](https://arxiv.org/html/2007.12655v2),
Definitions 3.1 and 3.10, distinguishes operator-MF approximation from weak
quasidiagonality: the latter requires unital completely positive maps from
the full group C*-algebra. Proposition 3.19 assumes weak quasidiagonality
and property (T) and, for an infinite group, concludes that an infinite
residually finite quotient exists. It does not state this with MF in place
of weak quasidiagonality. The introduction nevertheless prints
“MF ⇒ weak quasidiagonality” as clear from definitions. The introduction
also records the then-open existence of non-MF groups; Section 3 records
infinite simple Kazhdan groups that are not weakly quasidiagonal. These
passages cannot all serve as a consistent theorem package with the printed
arrow. The arrow has not been justified by the inspected argument.

[Ioana–Spaas–Wiersma, arXiv:2006.01874v2](https://arxiv.org/abs/2006.01874v2)
proves failures of lifting properties for full group C*-algebras, including
the failure of LLP for `Z² ⋊ SL₂(Z)` and `SL_n(Z)`, `n ≥ 3`. Thus a lifting
argument requires its own hypotheses. These results are not counterexamples
to the existential implication MF implies weak quasidiagonality.

## 2. The direction that follows from the definitions

Suppose `G` has unital completely positive maps
`phi_n : C*(G) -> M_(d_n)` whose multiplicative defects tend to zero in
operator norm and which separate the canonical group unitaries. Set
`a_n(g) = phi_n(u_g)`. Positivity gives

```text
a_n(g^(-1)) = a_n(g)*,       ||a_n(g)|| <= 1.
```

Asymptotic multiplicativity applied to `(g^(-1),g)` and `(g,g^(-1))` gives

```text
||a_n(g)* a_n(g) - I|| -> 0,
||a_n(g) a_n(g)* - I|| -> 0.
```

For each fixed `g`, the matrices are eventually invertible. Their polar
unitaries

```text
v_n(g) = a_n(g) (a_n(g)* a_n(g))^(-1/2)
```

satisfy `||v_n(g)-a_n(g)|| -> 0`, by continuous functional calculus on an
interval about `1`. Define the finitely many earlier values arbitrarily in
the unitary group, and take `v_n(e)=I`. For each `g,h`, the triangle
inequality gives

```text
||v_n(gh)-v_n(g)v_n(h)||
 <= ||v_n(gh)-a_n(gh)||
  + ||a_n(gh)-a_n(g)a_n(h)||
  + ||a_n(g)-v_n(g)|| + ||a_n(h)-v_n(h)|| -> 0.
```

The group-element separation survives the norm perturbation. Hence

```text
weakly quasidiagonal  =>  operator MF.
```

This calculation proves one direction only. A converse would be an
additional mathematical assertion.

## 3. An MF witness need not admit a completely positive extension

The obstruction is visible already for `G=C_2={e,s}`. For `n>=1`, define

```text
v_n(e)=I_2,       v_n(s)=diag(-1, exp(i/n)).
```

All multiplicative defects vanish except possibly that for `(s,s)`, whose
norm is `|exp(2i/n)-1| -> 0`. Also `||v_n(s)-I_2||=2`, so this is a
separating operator-MF approximation. However, `u_s=u_s*` in `C*(C_2)` and
`v_n(s)` is not selfadjoint. A positive linear map preserves adjoints, so
no `v_n` extends to a unital completely positive map on `C*(C_2)`.

More generally, if a unital completely positive map sends each canonical
group unitary to an actual unitary, every such unitary lies in its
multiplicative domain. Its restriction to the group is therefore an exact
homomorphism. Approximate unitary homomorphisms cannot simply be declared
to have completely positive extensions.

This example isolates the missing operation; it is **not** a group-level
counterexample. `C_2` is weakly quasidiagonal using its genuine regular
representation. Proving the desired converse would require constructing a
different family of completely positive contractions, with the required
asymptotic multiplicativity and separation, for every group under
consideration. No such construction occurs in the inspected citation.

## 4. The valid Kazhdan consequence

Let `G` be weakly quasidiagonal, have property (T), and have no nontrivial
finite quotient. If `G` is infinite, the precise Proposition 3.19 supplies
an infinite residually finite quotient `q:G->Q`. Choose `x!=1` in `Q`.
There is a finite group `F` and a homomorphism `f:Q->F` with `f(x)!=1`.
Replacing `F` by `f(Q)`, the composite `f q` is a nontrivial finite
quotient of `G`, a contradiction. Thus `G` is finite. Its identity map
is then a finite quotient, forcing `G=1`.

Consequently, an infinite hyperbolic Kazhdan group without finite
quotients is not weakly quasidiagonal. Passing from this conclusion to
non-MF would require the converse of the arrow established in Section 2,
at least for these groups.

## 5. The MF direction that remains unconditional

Every countable residually finite group is operator MF. Enumerate its
nonidentity elements as `g_1,g_2,...` and choose finite quotient maps
`q_j:G->F_j` with `q_j(g_j)!=1`. Put

```text
N_n = intersection_(j<=n) ker(q_j),
rho_n = left regular representation of G/N_n, composed with G -> G/N_n.
```

Each `rho_n` is an exact finite-dimensional unitary representation. For
`n>=j`, `g_j` moves the basis vector at the identity coset to a distinct
basis vector, so

```text
||(rho_n(g_j)-I) delta_(N_n)|| = sqrt(2).
```

The homomorphism `g -> [(rho_n(g))_n]` into the unitary group of the norm
matrix corona is therefore injective. Finite groups use the constant
sequence of their regular representations; the trivial group is
immediate. Thus a non-MF hyperbolic group is not residually finite, since
hyperbolic groups are finitely generated and hence countable.

## 6. Graph consequence

`mf-to-weak-qd-citation-has-unproved-lifting-step` invalidates the existing
routes `mf-kazhdan-without-finite-quotients-citation`,
`simple-kazhdan-full-mf-radical-proof`, and
`exact-kazhdan-radical-kernel-cannot-be-lef-proof`, each of which applies the
same unproved MF-to-weak-QD passage. The mathematical target
`mf-kazhdan-group-without-finite-quotients-is-trivial` remains an open claim,
not a refuted claim. The route
`non-mf-hyperbolic-from-kazhdan-quotientless` remains a valid conditional
implication with that explicit prerequisite. The established replacement
is `weak-qd-kazhdan-quotientless-group-is-trivial`. None of these changes
constructs a non-residually-finite hyperbolic group.
