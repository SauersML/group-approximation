---
rg: 2
id: laurent-sln-fq-lattices-charfinite-proof
kind: route
title: Check the hypotheses of Bader--Boutonnet--Houdayer--Peterson Theorem A over F_q(t) and derive the character consequences
target: laurent-sln-fq-lattices-are-charfinite
requires:
  - elementary-groups-over-fg-rings-have-property-t
  - kazhdan-hs-instability-lives-on-properly-nonamenable-limits
---

Notation: `q = p^m` is a prime power, `n >= 3`, `K = F_q(t)`,
`R = F_q[t,1/t]` and `A_(n,q) = SL_n(R)`.  `v_0` is the `t`-adic place of
`K` and `v_inf` the `1/t`-adic place.  `U_ij = {e_ij(x) : x in R}` for
`i != j`, where `e_ij(x) = I + x E_ij`.

## Sources

**Primary source (imported).**  U. Bader, R. Boutonnet, C. Houdayer,
J. Peterson, *Charmenability of arithmetic groups of product type*,
arXiv:2009.09952v3 (12 April 2022; Invent. Math. 229 (2022) 929--985).
Read on 2026-09-16 from the arXiv TeX source `main.tex`.  All quotations are
the TeX source, transcribed verbatim.

Definition of characters and their types (unlabelled `defn`, Section 1):

> A character $\phi$ on $\Gamma$ is called {\em amenable} if the corresponding
> GNS representation $(\pi,H)$ is amenable in the sense of \cite{Be89}, that
> is, $\pi \otimes \overline \pi$ weakly contains the trivial representation.
> It is called {\em von Neumann amenable} if $\pi(\Gamma)\dpr$ is moreover an
> amenable von Neumann algebra. It is called {\em finite} if $H$ is finite
> dimensional.

Earlier in Section 1, characters are the `Gamma`-fixed points of `PD_1(Gamma)`
under conjugation:

> Its compact convex subset consisting of $\Gamma$-fixed points is denoted by
> $\Char(\Gamma)$ and its elements are called {\em characters}

Definition `def:charmenable`:

> The group $\Gamma$ is said to be {\em charmenable} if it satisfies the
> following two properties:
> \begin{enumerate}
> \item Every non-empty compact convex $\Gamma$-invariant subset of
> $\PD_1(\Gamma)$ contains a character.
> \item Every extremal character of $\Gamma$ is either supported on the
> amenable radical $\Rad(\Gamma)$ or von Neumann amenable.
> \end{enumerate}
> Moreover, $\Gamma$ is said to be {\em charfinite} if it also satisfies the
> following properties:
> \begin{enumerate} \setcounter{enumi}{2}
> \item $\Rad(\Gamma)$ is finite.
> \item $\Gamma$ has a finite number of isomorphism classes of unitary
> representations in each given finite dimension.
> \item Every amenable extremal character of $\Gamma$ is finite.
> \end{enumerate}

Definition `def:arith`, excerpt:

> Let $K$ be a global field and ${\bf G}$ a connected non-commutative
> $K$-almost simple $K$-algebraic group.
> Let $S$ be a (possibly empty, possibly infinite) set of non-archimedean
> inequivalent absolute values on $K$,
> let $\mathcal{O}<K$ be the ring of integers and let $\mathcal{O}_S$ the
> corresponding localization,
> that is,
> \[ \mathcal{O}_S = \{ \alpha\in K\mid \forall s\in S, s(\alpha) \leq 1\}.  \]
> Fix an injective $K$-representation $\rho:{\bf G} \to \GL_n$ and denote
> \[ \Lambda_S=\rho^{-1}(\GL_n(\mathcal{O}_S))\le {\bf G}(K). \]
> The triple $(K,{\bf G},S)$ is said to be
> \begin{itemize}
> \item \emph{of a compact type}
> if for every absolute value $v$ on $K$, the image of $\Lambda_S$ in
> ${\bf G}(K_v)$ is bounded,
> \item \emph{of a simple type}
> if there exists a unique absolute value $v$ on $K$ such that the image of
> $\Lambda_S$ in ${\bf G}(K_v)$ is unbounded
> \item and \emph{of a product type} otherwise.

and, after the higher-rank sentence,

> A subgroup $\Gamma\le {\bf G}(K)$ is called \emph{$S$-arithmetic}
> if it is commensurable with $\Lambda_S$.
> It is called \emph{arithmetic} if it is $S$-arithmetic for some $S$ as above
> and we regard its type as the type of $(K,{\bf G},S)$.

Theorem `thm:AG`, printed as Theorem A:

> Let $K$ be a global field and ${\bf G}$ a connected non-commutative
> $K$-almost simple $K$-algebraic group.
> If $\Gamma\leq {\bf G}(K)$ is an arithmetic subgroup of a product type
> then $\Gamma$ is charmenable.
>
> Assume further that there exists an absolute value $v$ on $K$ such that
> ${\bf G}(K_v)$ has property {\em (T)} and for which the image of $\Gamma$
> in ${\bf G}(K_v)$ is unbounded.
> If either $S$ is finite or ${\bf G}$ is simply connected then
> $\Gamma$ is charfinite.

Lemma `soft charm`, statement (Section 3.1; cited by label because its printed
number was not checked):

> Every character of a charmenable group $\Gamma$ is a convex combination of a
> von Neumann amenable character and a character supported on $\Rad(\Gamma)$.

Proposition `prop:NST`, statement (Section 3.1):

> Every normal subgroup $N \lhd \Gamma$ of a charmenable group is amenable or
> co-amenable in $\Gamma$.
> If further $\Gamma$ is a charfinite group then $N$ is finite or of finite
> index in $\Gamma$.

The source also works in positive characteristic.  In the proof of its
finiteness-of-representations proposition (Section 7.1) it says:

> as if $K$ is of positive characteristic then every homomorphism
> $\rho:\Gamma\to \U(n)$ is finite
> by \cite[VIII(C), p.\ 259]{Ma91}.

Step 5 below re-proves this for the groups at hand, without Margulis.

**Cross-check (not used in the derivation).**  A. Dogon, M. Glasner,
Y. Gorfine, L. Hanany, A. Levit, *Non-uniform higher-rank lattices are
character rigid*, arXiv:2507.21862v1 (29 July 2025), TeX source
`arXiv_v1.tex`, read on 2026-09-16.  Its semisimple groups are products of
groups of `k_i`-points over arbitrary local fields.  Its Theorem
`main_thm_general`, case (2), assumes a non-compact factor with property (T)
and has no characteristic restriction.  The proof in Section 8 says:

> In fact $\Gamma$ enjoys  a stronger property, namely $\Gamma$ is
> \textit{charfinite} in the sense of \cite[Definition~1.2]{BBHP}. This is
> established in \cite[Theorem~A]{BBHP} in case $\Gamma$ is of
> \emph{product type} (namely, the semisimple group $H$ is not almost simple)

Its Definition `def:character rigidity`:

> A discrete group $\Gamma$ is  \textit{character rigid} if every character
> of $\Gamma$ is either finite-dimensional (i.e. is of the form
> $\frac{1}{\dim \pi} \mathrm{tr} \circ \pi$ for some finite-dimensional
> irreducible unitary representation $\pi$), or vanishes outside the center
> $\mathrm{Z}(\Gamma)$.

In that paper a character is an indecomposable trace.

## Step 1. The hypotheses of Theorem A (CF0)

Let `Gamma <= SL_n(K)` be commensurable with `A_(n,q)`.

**(a) Field and group.**
- `K = F_q(t)` is a global function field, and all of its absolute values are
  non-archimedean.
- `G = SL_n` is connected, non-commutative, absolutely almost simple and
  simply connected.  These are the standard structural facts about `SL_n`.

**(b) The arithmetic group.**  Take `rho` to be the inclusion
`SL_n -> GL_n`.
- The places of `K` are `v_inf` and the places `v_f` for monic irreducible
  `f in F_q[t]`; `v_0 = v_t`.
- Under the formula displayed in `def:arith`, take `S` to be the set of all
  places other than `v_0` and `v_inf`.  Then `O_S = R`.
  - If `alpha = g/h` in lowest terms and some irreducible `f != t` divides
    `h`, then `|alpha|_f > 1`.
  - Conversely, `g/t^k` is `f`-integral for every `f != t`.
- Under the usual convention, where `O_S` means functions regular outside
  `{v_0, v_inf}`, the ring is again `R`.
- Either way `Lambda_S = SL_n(K) ∩ GL_n(R) = SL_n(R)`, since a determinant-one
  matrix over `R` has its inverse over `R` by the adjugate.

**(c) Product type.**
- **Bounded away from `v_0, v_inf`.**  For every other place `v`,
  `R ⊆ O_v`, so the image of `Lambda_S` lies in the compact group `SL_n(O_v)`.
- **Unbounded at `v_0` and `v_inf`.**  Let `h = diag(t, t^(-1), 1, ..., 1)`.
  The matrix `h^k` has entries `t^k` and `t^(-k)`, and
  `|t^(-k)|_(v_0) = q^k -> inf` while `|t^k|_(v_inf) = q^k -> inf`.
- So exactly two places have unbounded image.  `(K, SL_n, S)` is neither of
  compact type nor of simple type, hence of product type.
- `Gamma` is commensurable with `Lambda_S`, so it is an arithmetic subgroup of
  product type.

**(d) An unbounded place with property (T).**  Take `v = v_0`, so
`G(K_v) = SL_n(F_q((t)))`.

*Lemma.*  Let `f: Delta -> G` be a homomorphism from a finitely generated
Kazhdan group into a locally compact group with dense image.  Then `G` has
property (T).

*Proof.*
- Let `(S_Delta, eps)` be a Kazhdan pair for `Delta` and put
  `Q = f(S_Delta)`, a finite and hence compact set.
- Let `pi` be a continuous unitary representation of `G` with a unit vector
  that is `(Q, eps)`-invariant.  That vector is `(S_Delta, eps)`-invariant for
  `pi∘f`, so there is a nonzero `pi∘f(Delta)`-invariant vector `eta`.
- The stabilizer `{g : pi(g) eta = eta}` is closed by strong continuity and
  contains the dense set `f(Delta)`, so it is all of `G`.  ∎

*Application.*
- `R` is a finitely generated ring, generated by `t`, `1/t` and a generator of
  `F_q^×`.  By `elementary-groups-over-fg-rings-have-property-t`,
  `Delta = EL_n(R)` has (T).
- `R` is dense in `F_q((t))`, since every Laurent series is the limit of its
  truncations, which lie in `R`.
- Each `x -> e_ij(x)` is continuous.  So the closure of `Delta` in
  `SL_n(F_q((t)))` contains every elementary matrix over `F_q((t))`.
- `SL_n` of a field is generated by elementary matrices (Gaussian
  elimination).  So `Delta` is dense, and `SL_n(F_q((t)))` has (T).

The image of `Gamma` at `v_0` is unbounded.  The subgroup `H = Gamma ∩ A_(n,q)`
has finite index in `A_(n,q)`, so among `h^0, ..., h^[A:H]` two lie in the same
coset.  Hence `h^m in Gamma` for some `m >= 1`, and the powers `h^(mk)` are
unbounded at `v_0` by (c).

**(e) Conclusion.**  `SL_n` is simply connected, so the charfinite clause of
Theorem A applies whether `S` is read as the infinite set of (b) or as
`{v_0, v_inf}`.  Hence `Gamma` is charfinite.  This is (CF0).

## Step 2. The radical (CF1)

By item 3, `Rad(Gamma)` is finite.  Let `N ⊴ Gamma` be finite.
- The centralizer `C = C_Gamma(N)` is the kernel of `Gamma -> Aut(N)`, so it has
  finite index in `Gamma`.  Hence `C ∩ A_(n,q)` has finite index in `A_(n,q)`.
- For `i != j`, `U_ij ∩ C` has finite index in the infinite group
  `U_ij ≅ (R, +)`.  So it contains some `e_ij(x)` with `x != 0`.
- If `g in N` commutes with `I + x E_ij` and `x != 0` in the field `K`, then
  `g E_ij = E_ij g`.  Entrywise, `(g E_ij)_(kl) = g_(ki) δ_(jl)` and
  `(E_ij g)_(kl) = δ_(ik) g_(jl)`.  Taking `l = j` gives `g_(ki) = 0` for
  `k != i` and `g_(ii) = g_(jj)`.
- Doing this for all `i != j` makes `g = λ I` with `λ^n = 1`.  So `λ` is
  algebraic over `F_q`, and `F_q` is algebraically closed in `F_q(t)`, so
  `λ in mu_n(F_q)`.

So every finite normal subgroup lies in `Gamma ∩ mu_n(F_q)·I`.  That group is
itself normal and abelian, hence contained in `Rad(Gamma)`.  Therefore
`Rad(Gamma) = Gamma ∩ mu_n(F_q)·I`.  For `(n,q) = (3,2)`,
`mu_3(F_2) = {1}`, so `Rad(A_(3,2)) = {e}`.

## Step 3. Extremal dichotomy (CF2)

Let `phi` be an extremal character that is not supported on `Rad(Gamma)`.
- By item 2 it is von Neumann amenable, hence amenable, since the quoted
  definition makes von Neumann amenability amenability "moreover".
- By item 5 it is finite: its GNS space `H` is finite-dimensional.
- The vector state `tau = <. xi, xi>` of the GNS vector is tracial on
  `M = pi_phi(Gamma)''`, because `phi(gh) = phi(hg)` and the state is weakly
  continuous.  It is faithful on `M`: if `tau(x*x) = 0` then
  `||x pi(g) xi||^2 = tau(pi(g)* x*x pi(g)) = tau(x*x) = 0` for all `g`, and
  `xi` is cyclic, so `x = 0`.
- `M` is a factor.  If `z` were a central projection with `0 < z < 1`, then
  `0 < tau(z) < 1` by faithfulness, and `phi = tau(z)·phi_z +
  tau(1-z)·phi_(1-z)` with `phi_z(g) = tau(pi(g)z)/tau(z)` a character.
  Extremality forces `phi_z = phi`, so `tau(xz) = tau(z)tau(x)` on the span of
  `pi(Gamma)`, hence on `M` by weak continuity; `x = z` gives
  `tau(z) = tau(z)^2`, a contradiction.
- So `M` is a finite-dimensional factor `M_k(C)`, whose unique tracial state
  is `tr_k`.
- So `phi = tr_k∘pi`, where `pi: Gamma -> U(k)` is the corresponding
  irreducible component.

Otherwise `phi` is supported on `Rad(Gamma)`, which is contained in
`Z(Gamma)` by Step 2.  This is (CF2), and it is character rigidity in the
DGGHL sense.

## Step 4. Normal subgroups (CF3)

By `prop:NST`, a normal subgroup of the charfinite group `Gamma` is finite or
of finite index.  If it is finite, Step 2 makes it scalar, hence central.

## Step 5. Finite images (CF4)

Let `rho: Gamma -> U(d)` be a unitary representation.
- `H = Gamma ∩ A_(n,q)` has finite index in `A_(n,q)`, so `U = H ∩ U_12` has
  finite index in `U_12 ≅ (R, +)`.  So `U` is an infinite elementary abelian
  `p`-group.
- `rho(U)` consists of commuting unitaries of order dividing `p`.  They are
  simultaneously diagonalizable with eigenvalues in `mu_p(C)`, so
  `|rho(U)| <= p^d`.
- Hence `ker rho ∩ U` is infinite, and `ker rho` is an infinite normal
  subgroup.  By Step 4 it has finite index, so `rho(Gamma)` is finite.

## Step 6. Trace decomposition for `A = SL_3(F_2[t,1/t])` (CF5)

**(i) Property (T).**
- `R = F_2[t,1/t]` is Euclidean for `N(g) = deg g - ord_t g`.
  - Write `a = t^l a_0` and `b = t^k b_0` with `a_0, b_0 in F_2[t]` and
    `a_0(0), b_0(0) != 0`.
  - Divide `a_0 = Q b_0 + r_0` in `F_2[t]`.
  - Then `a = t^(l-k) Q b + t^l r_0`, and `N(t^l r_0) <= deg r_0 < N(b)`.
- By row reduction, `SL_3(R) = EL_3(R)`: over a Euclidean ring every
  determinant-one matrix is a product of elementary matrices.
- So `A` has (T) by `elementary-groups-over-fg-rings-have-property-t`.
- `A` is infinite, so it is not amenable, since an amenable discrete group
  with (T) is finite.

**(ii) ICC.**
- Let `F` be the FC-centre of `A`.  Every finitely generated subgroup of `F`
  has a centre of finite index, namely the intersection of the finite-index
  centralizers of its generators.  So it is virtually abelian.
- Therefore `F` is amenable and normal, so `F ⊆ Rad(A) = {e}` by Step 2.
- Hence `A` is ICC and `L(A)` is a II_1 factor.

**(iii) Existence of the decomposition.**
- `A` is charmenable by Step 1.  By Lemma `soft charm`, a character `phi` is
  `phi = s·phi_1 + (1-s)·phi_2`, where `phi_1` is supported on `Rad(A) = {e}`
  and `phi_2` is von Neumann amenable.
- Normalization forces `phi_1 = delta_e`.
- The GNS algebra of `phi_2` is amenable, i.e. injective.  So by (A1) of
  `kazhdan-hs-instability-lives-on-properly-nonamenable-limits`, applied to
  the Kazhdan group `A`, `phi_2 = sum_i t_i·tr_(k_i)∘rho_i` with irreducible
  finite-dimensional `rho_i`.
- Grouping equivalent `rho_i` gives the displayed form with pairwise
  inequivalent `pi_i`.  Each has finite image by Step 5.

**(iv) The GNS algebra.**  Write `phi = sum_j λ_j phi_j` with `λ_j > 0`.  Here
`phi_j` runs over `delta_e` (if `s > 0`) and the `tr_(k_i)∘pi_i` with
`c_i > 0`, with GNS triples `(pi_j, H_j, xi_j)`.

1. **The summands are pairwise disjoint.**
   - `pi_(delta_e)` is the left regular representation `lambda`, and
     `lambda(A)'' = L(A)`.
   - The GNS representation of `tr_k∘pi_i` is `pi_i ⊗ 1` on `M_k(C)` with the
     normalized Hilbert--Schmidt inner product.  It is a multiple of `pi_i`
     and generates `M_k(C)`.
   - Multiples of inequivalent irreducibles are disjoint by Schur's lemma.
   - `lambda` has no nonzero finite-dimensional subrepresentation, because `A`
     is infinite.  If `P` projects onto an invariant subspace of dimension
     `r`, then `x -> ||P delta_x||^2` is `A`-invariant with sum `r`, hence
     identically `0`.  An intertwiner `T` from `lambda` to a
     finite-dimensional representation would make the closure of the range of
     `T*` such a subspace, so `T = 0`.
2. **The GNS representation of `phi` is the direct sum.**
   - Put `pi = ⊕ pi_j` and `xi = ⊕ λ_j^(1/2) xi_j`.  Then
     `<pi(g)xi, xi> = phi(g)`.
   - Disjointness gives `pi(A)' = ⊕ pi_j(A)'`, so the projections `z_j` onto
     the `H_j` lie in `pi(A)''`.
   - The cyclic subspace of `xi` therefore contains
     `z_j pi(A)'' xi = pi_j(A)'' xi_j`, whose closure is `H_j` for every `j`.
   - So `pi_phi ≅ pi`, and
     `pi_phi(A)'' = (⊕ pi_j(A)')' = ⊕ pi_j(A)'' = L(A) ⊕ ⊕ M_(k_i)(C)`.
3. **Uniqueness.**
   - Every summand is a factor, so the `z_j` are the minimal central
     projections.
   - Each weight is `λ_j = <z_j xi, xi>`, and each component is
     `phi_j = <pi(.) z_j xi, xi>/λ_j`.
   - The infinite-dimensional summand gives `delta_e`, and the representation
     on a finite-dimensional summand fixes `pi_i` up to equivalence.
   - So any second decomposition of the same form produces the same weights
     and components.

## Step 7. Limit algebras (CF6)

Let `sigma_n` be an asymptotic representation of `A` along `omega`.
- **The limit trace is a character.**  `sigma^omega: A -> U(M^omega)` is a
  homomorphism into the tracial ultraproduct, and `tau = tau_omega∘sigma^omega`
  is normalized, positive definite and conjugation invariant.
- **`N_omega` is the GNS algebra of `tau`.**  `tau_omega` is faithful on
  `N_omega = sigma^omega(A)''`.  The standard form `L^2(N_omega, tau_omega)`,
  with cyclic vector `1`, realizes the GNS representation of `tau`, and
  `N_omega` acts faithfully on it.  So `N_omega ≅ pi_tau(A)''`.
- **The summands.**  By Step 6, `N_omega ≅ L(A) ⊕ ⊕_(c_i>0) M_(k_i)(C)`, with
  the `L(A)` summand present iff `s > 0`.  Its central projections are sums of
  the minimal ones `z_j`.
- **`L(A)` is not injective.**  A conditional expectation
  `E: B(l^2 A) -> L(A)` would give a state `tau∘E` that is invariant under
  `Ad lambda(g)`.  Restricted to `l^inf(A)`, it would be an invariant mean,
  contradicting (i).
- **Injective summands.**  Every `M_k(C)` summand is injective.  A summand
  containing `z_(delta_e)` is not injective, since compressing a conditional
  expectation by a central projection preserves injectivity.

So `N_omega` has no nonzero injective direct summand iff every `c_i = 0`,
i.e. `tau = delta_e`, and then `N_omega ≅ L(A)`.  Substituting this into (A3)
of `kazhdan-hs-instability-lives-on-properly-nonamenable-limits` gives the
stated equivalence for flexible and for strict HS-stability.  ∎
