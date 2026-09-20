# Product traces and the exact full-shift Baum–Connes remainder

Date: 2026-09-20. Integrated from the user-supplied report *Cairn,
nonhyperlinearity, and the Baum–Connes problem*, Sections 8–10 and 12.4.
Written proof; not a Lean certificate or an independent referee report.
No novelty priority is claimed. The [integration ledger](bc-nonhyperlinearity-integration-2026-09-20.md)
records the existing inputs and the remaining ordinary assembly problem.

## 1. Setting, finite ranks, and the cylinder retraction

Let G be countable, Λ a finite alphabet with distinguished symbol 0,
X=Λ^G, X⁰=X\{0}, and A=C₀(X⁰)⋊ᵣG. The action is left translation of
coordinates. For now G need not be torsion-free. On ℓ²G use

```text
π_x(f)δ_h = f(h⁻¹x)δ_h,    π_x(u_g)δ_h = δ_(hg⁻¹).
```

If x has finite support, π_x(A) consists of compact operators. For a
locally constant f vanishing at zero with coordinate window W,
f(h⁻¹x)≠0 requires hW to meet supp(x), leaving finitely many h.
Density proves the assertion for all coefficients and then for A.
Write r_x:K₀(A)→ℤ for rank, set r₀=0, and put

```text
K₀^inv(A) = ⋂_(x of finite support) ker r_x.
```

For a probability ν on Λ, μ=ν^G is invariant; τ_μ=μ∘E is a trace on A.
Throughout, its matrix extension uses Tr_m, not Tr_m/m.

When G is torsion-free, let S be the nonempty finitely supported
patterns with nonzero symbols. Their cylinders C_s allow arbitrary
symbols outside their supports. The equivariant comparison is the
stabilized *-homomorphism

```text
Θ:c₀(S) → K(ℓ²S)⊗C₀(X⁰),    δ_s ↦ e_ss⊗1_(C_s).
```

The diagonal matrix factors are necessary because cylinders overlap.
The K₀ map after descent and Morita equivalence is
T:⊕_(G\S)ℤ→K₀(A), [s]↦[1_(C_s)]. It is injective by the minimal-support
rank argument in [the rank-functional proof](bc-bernoulli-rank-functionals-2026-09-13.md).
The [locality proof](bc-bernoulli-rank-locality-2026-09-13.md) gives

```text
n_[s](y) = Σ_(U⊆F_s) (-1)^|F_s\U| r_(s|U)(y),
N(y)=(n_[s](y)) ∈ ⊕_(G\S)ℤ,
NT=1,  ker N=K₀^inv(A),
K₀(A)=T(⊕_(G\S)ℤ) ⊕ K₀^inv(A).
```

Here finiteness is a theorem: far-site mixed rank differences are
exponentially small integers, so the nonzero coefficients have bounded
diameter and only finitely many pattern orbits. It is not an assumption
that all analytic K-classes are cylinders.

## 2. Uniform finite-block relative spectral traces

The clopen compact subsets of X⁰ provide an approximate unit of
projections for C₀(X⁰) and for A. For an algebraic crossed-product term,
left and right multiplication converge because this is an approximate
unit in the coefficient algebra and its translates also converge.
Thus every K₀ class is a difference of actual matrix projections over A.

For a projection p∈M_m(A), choose a self-adjoint algebraic approximation

```text
a=Σ_(g∈E) f_g u_g,    ||a-p||<1/8,
```

where E is finite and contains the identity, every f_g is locally constant
on one finite coordinate window W, and f_g(0)=0. Put A_x=π_x(a).
Every spectrum is contained in J₀=[−1/8,1/8] and J₁=[7/8,9/8].
Let P_x=f(A_x), where f is zero near J₀ and one near J₁. The projection
f(a) is homotopic to p through spectral cuts of the segment joining p
and a, whose gap at 1/2 remains open.

Replacing a symbol at the identity changes A_x by a self-adjoint
operator Δ_s(x)=A_(x^{e,s})−A_(x^{e,0}) supported on the fixed finite
block W⁻¹E (enlarge W to contain e). Rows can change only at W⁻¹;
self-adjointness also controls columns. Its rank is at most m|W|,
its norm at most 2||a||, and it depends on finitely many coordinates.
For a fixed contour Γ enclosing J₁ and avoiding J₀,

```text
P_(x^{e,s})−P_(x^{e,0})
  = (1/2πi) ∮_Γ (z−A_(x^{e,s}))⁻¹ Δ_s(x)
                     (z−A_(x^{e,0}))⁻¹ dz.
```

The difference is trace class, with a uniform trace-norm bound. Define
D_s^p(x)=Tr(P_(x^{e,s})−P_(x^{e,0})). This function is bounded and
continuous on X. Indeed, converging configurations give strong-* convergence
of these uniformly bounded finite-propagation operators, and strong-*
convergence of their resolvents on the common contour. Δ_s(x) is eventually
constant in a fixed finite block. Products of the resolvents with that
block converge in trace norm; contour integration and the uniform bound
give the claimed continuity.

For y=[p]−[q], subtract to obtain D_s^y. At finite configurations,

```text
D_s^y(x)=r_(x^{e,s})(y)−r_(x^{e,0})(y).
```

If y∈K₀^inv(A), these values vanish. Finite configurations are dense, hence
D_s^y vanishes everywhere. It remains to relate these relative traces
to differentiation of the product-measure trace.

## 3. Polynomial differentiation with no infinite-volume limit

Set ν_θ=(1−θ)δ₀+θν and μ_θ=ν_θ^G for 0≤θ≤1. For a polynomial h with
h(0)=0, the root diagonal of h(A_x) depends on finitely many coordinates.
Differentiating its finite product integral gives

```text
d/dθ τ_(μ_θ)(h(a))
 = Σ_(s∈Λ) ν(s) ∫ Tr(h(A_(x^{e,s}))−h(A_(x^{e,0}))) dμ_θ(x).   (1)
```

To verify the equality, first differentiate over each coordinate v in
the finite dependency set. The derivative of ν_θ is ν−δ₀. Covariance
A_(gx)=L_g A_x L_g⁻¹ and invariance of μ_θ turn the root diagonal of a
change at v into the diagonal at v⁻¹ of a change at e. Summing over v
is the operator trace in (1). This sum is finite: expanding a difference
of powers inserts Δ_s between finitely many finite-propagation factors,
so only finitely many diagonal entries can be nonzero. No Følner
sequence, amenability, or growth estimate is used.

## 4. Passing to projections controls relative trace norms

Uniform approximation only on the real spectrum would not justify
convergence of the derivatives in (1). Instead use explicit polynomials

```text
c_k = binom(2k,k)/4^k,
h_N(z) = (1+(2z−1) Σ_(k=0..N) c_k(1−(2z−1)²)^k)/2.
```

Each h_N(0)=0. On either complex disk of radius 1/6 centered at 0 or 1,
|1−(2z−1)²|≤7/9. The binomial series converges uniformly there; h_N
converges to 0 on the first disk and to 1 on the second. The sign is
determined at the centers and is constant on each connected disk.
Denote this locally holomorphic limit by f.

Both spectral intervals are at least 1/24 from the boundary circles,
so the resolvents on them have norm at most 24. Cauchy's formula on
the two circles, followed by the resolvent identity, gives

```text
||(h_N−f)(A_(x^{e,s}))−(h_N−f)(A_(x^{e,0}))||₁
 ≤ C ||Δ_s(x)||₁ ε_N,
```

where ε_N is the supremum error on the circles and tends to zero;
C is independent of x, s, N. Thus the relative polynomial differences
converge uniformly in trace norm to the relative spectral projections.
Also h_N(a)→f(a) in C*-norm. In (1) the functions and their derivatives
therefore converge uniformly for θ∈[0,1]. The limiting derivative is

```text
d/dθ τ_(μ_θ)([p]) = Σ_s ν(s) ∫ D_s^p(x) dμ_θ(x).              (2)
```

The right side is continuous: D_s^p is continuous on compact X and
μ_θ varies weakly continuously, as is seen first on cylinder functions
and then by uniform approximation. Alternatively integrate (1) and
pass to uniform limits in the fundamental theorem of calculus to get (2).

For rank-invisible y, D_s^y=0. Its trace is constant in θ, and at θ=0
the all-zero configuration kills the entire ideal. Consequently

```text
τ_(ν^G)(y)=0   for every y∈K₀^inv(A).                         (3)
```

This proof of (3) does not require torsion-freeness. It applies to the
full shift and independent identically distributed product measures;
no correlated invariant measure or arbitrary subshift is covered.

## 5. Finite trace formula and the wreath-product range

Now assume G torsion-free. Subtract T(N(y)) and use (3) and Section 1:

```text
τ_(ν^G)(y)=Σ_[s] n_[s](y) ∏_(v∈F_s) ν(s(v)).                (4)
```

The sum is finite. With the uniform measure on p symbols its value
lies in ℤ[1/p]. If G is infinite, cylinders fixing a nonzero symbol
on n distinct sites have trace p⁻ⁿ for every n, so the ideal's trace
range is exactly ℤ[1/p].

Evaluation at zero has the equivariant constant section. The reduced
sequence stays split exact, even for a nonexact host. Hence

```text
K_*(C(X)⋊ᵣG) ≅ K_*(C*ᵣG) ⊕ K_*(A).
```

Fourier duality for X=widehat(⊕_G C_p) identifies its Haar trace with
the canonical group trace for W=C_p wr G. For infinite countable
torsion-free G and prime p,

```text
τ_W(K₀(C*ᵣW)) = τ_G(K₀(C*ᵣG)) + ℤ[1/p].                    (5)
```

No assembly conjecture is assumed here. Every finite subgroup of W
lies in the lamp kernel, and arbitrarily large finite p-lamp subgroups
exist, so Λ_W=ℤ[1/p]. If host assembly is surjective, its trace range
is ℤ by the torsion-free assembly trace theorem. Equation (5) then
equals Λ_W. Haar trace cannot detect a new full-shift defect beyond
the host.

## 6. The exact remaining assembly groups

The host splitting, the stabilized weak K-equivalence, going-down,
and the amenable-kernel partial-assembly isomorphism identify assembly
for W with the direct sum of host assembly and the cylinder comparison.
The punctured part has topological groups ⊕_(G\S)ℤ in degree zero and
zero in degree one. The retraction N gives

```text
ker μ_(W,j) ≅ ker μ_(G,j),                         j=0,1,
coker μ_(W,0) ≅ coker μ_(G,0) ⊕ K₀^inv(A),
coker μ_(W,1) ≅ coker μ_(G,1) ⊕ K₁(A).
```

The named existing inputs are
`bernoulli-bc-splits-into-host-and-cylinder-comparison`,
`bernoulli-assembly-injective-beyond-the-host`,
`bernoulli-pattern-expansions-are-finite`, and
`amenable-kernel-bc-transfer-and-ktop-half-exactness`.

For a positive host, the wreath problem is exactly the vanishing of
K₀^inv(A) and K₁(A). A nonzero class in either extra summand refutes
ordinary surjectivity regardless of whether the host is decided.
Equation (3) does not prove K₀^inv(A)=0, and says nothing about K₁.
A positive projection of rank zero at all finite configurations is
zero, by continuity and faithfulness of conditional expectation;
a virtual difference of projections with equal ranks need not be zero.
The decreasing ideal tail is not an increasing inductive limit.

For finitely generated torsion-free G, restriction to the CND-support
shift also annihilates K₀^inv(A) and all odd classes: its coefficient
assembly is positive and its K-theory has the cylinder basis, detected
by finite CND configurations. This uses the Tu/going-down imports in
[the CND-support artifact](bc-cnd-support-shift-a-t-menable-2026-09-16.md),
not a new exactness assumption. Under that artifact's hypothesis (M),
the HLS class has no full-shift lift. Zero restriction does not identify
a class with the crossed product of the complementary open subset
without an additional reduced-exactness theorem.
