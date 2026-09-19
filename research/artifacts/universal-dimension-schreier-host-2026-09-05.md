# An explicit universal congruence host with sublinear regular-profile seeds

This supplies a positive complement to
`rectangular-seed-quotient-alignment-2026-09-05.md`. For exact inputs of
bounded dimension there is a single explicit congruence level; its
Schreier holonomy can always be chosen trivial. Along exact inputs with
regular limiting character, the seed dimension is sublinear in the input
dimension. The construction retains every constituent and has no frame
error. Constructing the frame from arbitrary approximate tuples remains
unproved.

## 1. An explicit universal level, without invoking superrigidity

For an integer `D>=1`, put

```text
q_D=lcm(1,2,...,floor(D^(1/3))),
N_D=Gamma(q_D)<=G=SL_5(Z),
Q_D=G/N_D.
```

Every genuine unitary representation `rho:G->U(d)` with `d<=D` kills
`N_D`. In particular it factors through the single finite quotient `Q_D`.

To prove this, fix distinct indices `i,j,l` and put

```text
A=rho(e_(il)(1)),
B=rho(e_(lj)(1)),
C=rho(e_(ij)(1)).
```

The elementary identities say `[A,B]=C` and that `C` commutes with both
`A` and `B`. Since `C` is unitary, its eigenspaces are orthogonal. Each
eigenspace `H_lambda` is invariant under `A,B` and their inverses. If
`r=dim H_lambda`, restricting the commutator identity and taking
determinants gives

```text
1=det([A|H_lambda,B|H_lambda])=lambda^r.
```

Here `1<=r<=d<=D`, so the eigenvalue has finite order `h` dividing `r`.
For `SL_5` there are three choices of `l` outside `{i,j}`. Write the
corresponding operators as `A_l,B_l`. The elementary identities give

```text
[A_l,A_m]=[B_l,B_m]=I,
[A_l,B_m]=C^(delta_(l,m)).
```

All these operators preserve `H_lambda`. Simultaneously diagonalize the
three commuting unitaries `A_l` there. If `v` has joint eigenvalues
`(a_l)_l`, then `B_m v` has the same eigenvalues except that its m-th
coordinate is multiplied by `lambda`, because
`A_l B_m=lambda^(delta_(l,m)) B_m A_l` on `H_lambda`.

Thus the occurring joint eigenvalues are partitioned into free orbits
under coordinatewise multiplication by `(Z/hZ)^3`. Each orbit contains
`h^3` distinct weights, and the corresponding weight spaces all have
equal dimension since the `B_m` are invertible. Consequently

```text
h^3 divides dim H_lambda,       h^3<=D.
```

Every eigenvalue order therefore divides the displayed `q_D`, and
`C^q_D=I`. This proves that `ker rho` contains every elementary matrix
`e_(ij)(q_D)` and, by powers, every `e_(ij)(a q_D)`.

The precise arithmetic input is

```text
E_5(Z,q_D Z)=SL_5(Z,q_D Z)=Gamma(q_D),                  (UH1)
```

where the left side is the normal closure in `E_5(Z)=SL_5(Z)` of the
elementary matrices with entries in `q_D Z`. Since `ker rho` is normal,
it contains that entire subgroup, proving the assertion.

For `(UH1)`, the primary source is Bass--Milnor--Serre, *Solution of the
congruence subgroup problem for SL_n (n>=3) and Sp_2n (n>=2)*,
Publications Mathématiques de l'IHÉS 33 (1967), pp.59--137:
[primary PDF](https://www.numdam.org/item/PMIHES_1967__33__59_0.pdf).
The opening of §4, printed p.94, defines `E_n(A,q)` as this normal
closure and defines `C_q=SL_n(A,q)/E_n(A,q)`. Corollary4.3(a),(b), printed
p.95, gives `E_n(A)=SL_n(A)` and `C_q=1` when `A` is not totally
imaginary. This applies to `A=Z` and all nonzero ideals, including even
levels. No assertion about a subgroup generated without taking normal
closure is being substituted here.

This also proves directly that every finite-dimensional unitary
representation of `SL_5(Z)` has finite image and that there are only
finitely many irreducibles of dimension at most `D`: all such irreducibles
belong to the one finite group `Q_D`. Thus neither superrigidity nor a
separate local-rigidity compactness argument is required for this step.
The initial one-pair determinant argument alone would give the weaker
universal level `lcm(1,...,D)`. The simultaneous-pair sharpening was
identified by the independent induction audit. For `SL_n(Z)`, `n>=3`,
the same proof has `n-2` independent pairs and gives the universal level
`lcm(1,...,floor(D^(1/(n-2))))`.

## 2. Exact frames and the smallest trivial seed at that host

Let `rho:G->U(d)`, `d<=D`, and decompose it as

```text
rho = direct_sum_sigma sigma tensor I_(m_sigma),
r_sigma=dim sigma.
```

All occurring irreducibles factor through `Q_D`. For a positive integer
`k`, take the trivial subgroup representation

```text
pi=1_(N_D) tensor I_k.
```

Its induced representation is

```text
Ind_(N_D)^G pi = lambda_(Q_D) tensor I_k.
```

The regular representation contains every irreducible `sigma` with
multiplicity `r_sigma`. Hence the exact smallest seed dimension admitting
an equivariant isometry from `rho` is

```text
k_min(rho)=max_(m_sigma>0) ceil(m_sigma/r_sigma).         (UH2)
```

This expression is independent of which larger universal level is used:
inflating an irreducible to a larger finite quotient does not change its
dimension or its multiplicity in that quotient's regular representation.
In particular `k_min<=d`, proving the universal `d`-copy host assertion.

For a complete construction, choose for each `sigma` an isometry between
its multiplicity space `C^(m_sigma)` and `C^(k r_sigma)`. Tensor these
maps with the identity on the irreducible spaces and take their direct
sum. This gives a `G`-equivariant isometry

```text
J:C^d -> l^2(Q_D) tensor C^k.
```

For a left-coset transversal `T` of `N_D`, take its coordinate maps

```text
A_t=(coordinate_t tensor I_k) J : C^d->C^k.
```

They satisfy

```text
sum_t A_t^* A_t=I_d,
A_(t')rho(s)=A_t    whenever s t=t' n(s,t).             (UH3)
```

These are exact `(MSC7)` data with trivial holonomy, `zeta=beta=0`.
No lower singular-value assumption, approximate subgroup representation,
or Schreier filling ledger is needed once the exact input is supplied.

## 3. Regular limiting character expels each fixed finite-dimensional type

Suppose `rho_j:G->U(d_j)` are genuine and their normalized characters
converge pointwise to the regular character:

```text
tr_(d_j)(rho_j(g)) -> 1_(g=e).                          (UH4)
```

Then, for every fixed `M`, the fraction of the representation carried by
irreducibles of dimension below `M` tends to zero.

Here is a proof using the same finite Kazhdan pair `(S,kappa)` as MSC.
Take `S` symmetric, write `h=|S|`, and for any genuine unitary
representation `theta` form the positive contraction

```text
L_theta=(I+(1/h)sum_(s in S)theta(s))/2.
```

On the orthogonal complement of the invariant vectors,

```text
< (I-L_theta)v,v >
 =(1/(4h))sum_s ||theta(s)v-v||^2
 >= c ||v||^2,             c=kappa^2/(4h)>0.            (UH5)
```

Fix an irreducible `sigma` of dimension `r` and apply this to
`theta_j=rho_j tensor conjugate(sigma)`. Its invariant dimension is
`m_j(sigma)`. Since `L_theta_j` is positive and equals the identity on
invariants, for every positive integer `a` we have

```text
m_j(sigma)/(d_j r) <= tr_(d_j r)(L_theta_j^a).
```

For fixed `a`, expansion of the finite word polynomial and `(UH4)` show
that the right side tends to `tau_G(L_lambda^a)`, where `lambda` is the
regular representation and `tau_G` its canonical trace. Indeed the
normalized character of `theta_j` also tends to `1_(g=e)`: its other
factor is the fixed normalized character of `conjugate(sigma)`.

The infinite group `G` has no invariant vector in its regular
representation. Thus `(UH5)` gives

```text
tau_G(L_lambda^a) <= (1-c)^a.
```

First let `j->infinity`, then `a->infinity`. It follows that

```text
m_j(sigma) r/d_j -> 0.                                 (UH6)
```

Section1 shows that only finitely many irreducibles have dimension below
any fixed `M`. Summing `(UH6)` over that finite collection proves

```text
epsilon_(j,M)
 =(1/d_j)sum_(r_sigma<M) m_j(sigma) r_sigma ->0.         (UH7)
```

Also `d_j->infinity`: otherwise a subsequence has `d_j<=D`, and Section1
makes every term kill the same nonidentity matrix `e_12(q_D)`, contrary
to `(UH4)`.

## 4. Sublinear seeds retain the entire exact representation

Let `k_j=k_min(rho_j)`. For a constituent with `r_sigma>=M`,

```text
m_j(sigma)/r_sigma <= d_j/r_sigma^2 <= d_j/M^2.
```

For one with `r_sigma<M`, its entire isotypic dimension is at most
`epsilon_(j,M)d_j`, so

```text
m_j(sigma)/r_sigma <= epsilon_(j,M)d_j.
```

The exact seed formula `(UH2)` therefore gives

```text
k_j/d_j <= max(epsilon_(j,M),1/M^2)+1/d_j.             (UH8)
```

For each fixed `M`, take the limit superior in `j`, using `(UH7)`.
Then let `M->infinity`. The conclusion is

```text
k_j/d_j ->0.                                          (UH9)
```

Choose the deterministic host `N_(d_j)=Gamma(q_(d_j))` and apply the
exact construction in Section2 with `k=k_j`. Thus every exact
regular-character sequence admits genuine trivial subgroup seeds of
dimension `o(d_j)` and exact Parseval frames, with no discarded
low-dimensional blocks and no enlargement of the represented input.
This holds for all exact sequences satisfying `(UH4)`, not just regular
representations of individual finite quotients.

If arbitrary tuples `U_(j,s)` are already within `eta_j->0` of such
same-dimensional exact `rho_j`, the same frames satisfy `zeta_j=0` and
`beta_j<=eta_j`, since `J_j` is an isometry. This is a consequence of
having the exact comparison; it is not a derivation of one from small
defining-relator defect.

The host index may be enormous. This artifact asserts existence and an
explicit universal level, not an efficient finite-quotient computation.
The remaining correction problem is to select sufficiently good frame
maps directly from the approximate tuple. QRC5 has not yet supplied that
selection. The coprime-level obstruction is therefore a constraint on
choosing a host, rather than an obstruction to the universal
dimension-dependent host established here.
