# Seed-radical transfer: central D8 marks, dual measures and coset-lamp fixed algebras (2026-09-16)

Swarm artifact for the hole `infinite-character-actor-word-energy-interface`.
It contains complete proofs of four statements.

- **Lemma A** (`central-d8-mark-radical-equals-seed-radical`). The central mark `J` of the D8 seed lies in the
  hyperlinear radical of the marked group exactly when the seed `b` lies in the hyperlinear radical of the base.
- **Lemma B** (`semidirect-seed-radical-is-ce-dual-measure-test`). For an abelian-by-hyperlinear semidirect
  product, a module element lies in the hyperlinear radical iff every invariant measure on the dual whose
  crossed product is Connes embeddable is carried by its annihilator.
- **Proposition C** (`coset-lamp-seed-radical-is-ce-fixed-algebra-rigidity`). For a permutational coset lamp
  over `C<A`, the two-point seed `delta_C+delta_(aC)` lies in the hyperlinear radical iff every p.m.p.
  `A`-action with Connes-embeddable crossed product has no `C`-invariant set moved by `a`.
- **Corollary D** (`homogeneous-quotient-ce-frees-sl3-lamp-seed`). If one of the open algebras `(SH1)` is
  Connes embeddable, the SL3 two-point lamp seed is outside the hyperlinear radical, the central mark `J`
  is outside the radical of the marked host, and the terminal estimate `(ICR2)` fails for that host.

Section 5 lists what is **not** claimed.

## 0. Conventions and standard facts

All groups are countable. A **tracial matrix ultraproduct** is `Q = prod_omega (M_(d_n), tr)` for a
nonprincipal ultrafilter `omega` on `N`, with normalized trace `tr` and `||x||_2 = tr(x^* x)^(1/2)`. Elements
of `U(Q)` are classes `[x_n]` of sequences of unitaries. The **hyperlinear radical** `Rad_hyp(G)` is the
intersection of the kernels of all homomorphisms `G -> U(Q)`, over all tracial matrix ultraproducts `Q`. It is
a normal subgroup. `G` is hyperlinear iff `Rad_hyp(G) = 1`. For a subgroup `H <= G`, restriction gives
`Rad_hyp(H) <= Rad_hyp(G) cap H`.

A finite von Neumann algebra `N` with faithful normal tracial state `tau` is **Connes embeddable (CE)** if
there is a trace-preserving unital `*`-homomorphism `N -> Q` into some tracial matrix ultraproduct. Such a map
is injective and isometric for `||.||_2`.

The commutator is `[x,y] = x y x^(-1) y^(-1)`.

**F1 (tensor estimate).** For unitaries `U, U' in U(d)` and `V, V' in U(e)`, with normalized traces,

```text
||U (x) V - U' (x) V'||_2 <= ||U-U'||_2 + ||V-V'||_2,     tr(U (x) V) = tr(U) tr(V).
```

*Proof.* `U(x)V - U'(x)V' = (U-U')(x)V + U'(x)(V-V')`, and `||X (x) W||_2 = ||X||_2` for unitary `W`. The
trace identity is multiplicativity of the normalized trace. By induction, for unitaries
`X_1,...,X_k, Y_1,...,Y_k` one has `||(x)X_i - (x)Y_i||_2 <= sum_i ||X_i - Y_i||_2`, and
`|prod x_i - prod y_i| <= sum |x_i - y_i|` for complex numbers of modulus at most one.

**F2 (lifting and diagonal ultraproducts).** If `theta : G -> U(prod_omega M_(d_n))` is a homomorphism with
unitary lifts `theta_n(g)`, then for every finite `F <= G` and `epsilon > 0` the set of `n` with

```text
max_(g,h in F) ||theta_n(g) theta_n(h) - theta_n(gh)||_2 < epsilon,
max_(g in F) |tr theta_n(g) - tau(theta(g))| < epsilon
```

belongs to `omega`; in particular it is nonempty, and finitely many such conditions can be met by one `n`.
Conversely, let `V_k : G -> U(D_k)` be maps such that, for every finite `F` and `epsilon > 0`, the displayed
multiplicative defect is below `epsilon` for all large `k`. Then for every nonprincipal `omega'` the map
`g -> [V_k(g)]` is a homomorphism `G -> U(prod_(omega') M_(D_k))` with trace `lim_(omega') tr V_k(g)`. If
`tr V_k(g) -> c(g)` for some `g`, that trace is `c(g)`. Both directions are immediate from the definitions.

**F3 (spectral measure of an abelian unitary family).** Let `M` be a countable abelian group, `theta : M -> U(Q)`
a homomorphism into a finite von Neumann algebra `(Q,tau)`, and `phi(m) = tau(theta(m))`. Then there is a
unique Borel probability measure `nu` on the compact metrizable dual `M^ = Hom(M,T)` with

```text
phi(m) = int e_m d nu,          e_m(chi) = chi(m).
```

*Proof.* The norm closure `B` of `span theta(M)` is a unital commutative C`*`-algebra. Every character `psi` of
`B` restricts to a character `chi_psi(m) = psi(theta(m))` of `M`. The map `psi -> chi_psi` is continuous and
injective, because `theta(M)` spans a dense subalgebra. Its domain is compact, so it is a homeomorphism onto a
closed set `Sigma <= M^`. Gelfand duality gives `B = C(Sigma)` with `theta(m)` corresponding to `e_m|Sigma`. The
Riesz theorem turns the state `tau|B` into a probability measure `nu` on `Sigma`, extended by zero to `M^`.

For uniqueness, `span{e_m}` is a unital `*`-subalgebra of `C(M^)`: `e_m e_(m') = e_(m+m')` and
`conj(e_m) = e_(-m)`. It separates points, so Stone--Weierstrass makes it dense. A measure is determined by its
integrals of the `e_m`.

**F4 (GNS extension).** Let `(N_i, tau_i)`, `i = 1,2`, be finite von Neumann algebras with faithful normal
tracial states. Let `sigma_i : G -> U(N_i)` be homomorphisms with `tau_1(sigma_1(g)) = tau_2(sigma_2(g))` for all
`g`, and let `W_i = W^*(sigma_i(G))`. Then there is a trace-preserving `*`-isomorphism `W_1 -> W_2` with
`sigma_1(g) -> sigma_2(g)`.

*Proof.* Let `S_i = span sigma_i(G)`, unital `*`-subalgebras. If `x = sum c_g sigma_1(g)`, then

```text
||sum c_g sigma_2(g)||_2^2 = sum_(g,h) c_g conj(c_h) tau_2(sigma_2(h^(-1) g)) = ||x||_2^2,
```

so `Phi(sum c_g sigma_1(g)) = sum c_g sigma_2(g)` is a well-defined, trace-preserving `*`-isomorphism
`S_1 -> S_2`, by faithfulness of the traces. Represent `W_i` on `L^2(W_i, tau_i)` with trace vector `Omega_i`. By
the Kaplansky density theorem, `S_i Omega_i` is dense in `L^2(W_i)`. The map `x Omega_1 -> Phi(x) Omega_2`
extends to a unitary `T : L^2(W_1) -> L^2(W_2)` with `T x T^* = Phi(x)` for `x in S_1`. Hence `Ad T` maps the
weak closure `S_1'' = W_1` onto `S_2'' = W_2` (bicommutant theorem in the standard representations). It
preserves the traces because `tau_i(y) = <y Omega_i, Omega_i>`.

**F5 (crossed products).** Let a countable group `A` act by measure-preserving Borel automorphisms on a standard
probability space `(Z, kappa)`, written `z -> bz`. The crossed product `N = L^infinity(Z,kappa) rtimes A` is
generated by `L^infinity(Z)` and unitaries `u_b` with `u_b f u_b^* = f o b^(-1)` and `u_b u_(b') = u_(bb')`. It has
the faithful normal trace `tau(f u_b) = delta_(b,1) int f d kappa`. This is standard and needs no freeness or
ergodicity.

**F6 (density of continuous functions).** If `nu` is a Borel probability measure on a compact metrizable space
`K` and `D <= C(K)` is a norm-dense unital `*`-subalgebra, then the von Neumann algebra generated by `D` in
`L^infinity(K,nu)` is `L^infinity(K,nu)`.

*Proof.* If `g in L^1(nu)` annihilates `C(K)`, then the measure `g d nu` is zero by uniqueness in the Riesz
theorem, so `g = 0`. By Hahn--Banach, `C(K)` is weak`*`-dense in `L^infinity(nu) = L^1(nu)^*`. The weak`*`
topology is the sigma-weak topology of multiplication operators on `L^2(nu)`.

**F7 (regular hyperlinear representation).** If `A` is hyperlinear, there is a homomorphism
`alpha' : A -> U(Q_alpha)` into a tracial matrix ultraproduct with `tau(alpha'(a)) = delta_(a,1)`.

*Proof.* For a unitary `U` in a finite von Neumann algebra, `||U - 1||_2^2 = 2 - 2 Re tau(U)`. So `U != 1` forces
`tau(U) != 1`, and then `|tau((U+1)/2)| = |tau(U)+1|/2 < 1` by strict convexity of the disc.

Enumerate `A - {1} = {a_1, a_2, ...}`. For each `i`, choose `theta^(i) : A -> U(Q_i)` with `theta^(i)(a_i) != 1`,
and put `beta^(i) = theta^(i) (+) 1`, a homomorphism into `M_2(Q_i)`, which is again a tracial matrix
ultraproduct. Let `c_i = |tau(beta^(i)(a_i))| < 1`. Enumerate `A = {g_1, g_2, ...}`.

For each `k`, choose by F2 levels of `beta^(1),...,beta^(k)` whose multiplicative defects on
`g_1,...,g_k` and trace errors on `g_1,...,g_k` are all below `1/k^3`. Put

```text
beta_k(g) = (x)_(i<=k) (beta^(i)_(level))(g)^((x) k),
```

a tensor product of `k^2` unitaries. By F1, its defect on `g_1,...,g_k` is at most `k^2/k^3 = 1/k`. Its trace
at `g` is within `1/k` of `prod_(i<=k) tau(beta^(i)(g))^k`. For fixed `a = a_i != 1` and `k >= i`, this product
has modulus at most `c_i^k`. Hence `tr beta_k(a) -> 0` for `a != 1`, while `beta_k(1) = I`. F2 gives `alpha'`.

## 1. Lemma A: the central D8 mark detects exactly the seed radical

Let `G` be a group and `b in G` with `b^2 = 1`. Put

```text
P(G,b) = < G, z, J | z^2 = J^2 = 1, J central, [b,z] = J >.        (CDS1)
```

**Lemma A.** `J in Rad_hyp(P(G,b))` iff `b in Rad_hyp(G)`. More precisely:

1. if `b in Rad_hyp(G)`, every homomorphism `P(G,b) -> U(Q)` kills `J`;
2. if `b notin Rad_hyp(G)`, there is a homomorphism `Theta : P(G,b) -> U(Q')` into a tracial matrix ultraproduct
   with `Theta(J) = -1`, and hence `||Theta(J) - 1||_2 = 2`.

When `b != 1`, `G` embeds in `P(G,b)` by `central-d8-seed-preserves-hyperlinearity`. The lemma does not use
that.

### Proof of 1

Let `Theta : P(G,b) -> U(Q)` be a homomorphism. Its restriction to `G` is a homomorphism `G -> U(Q)`, so
`Theta(b) = 1`, and `Theta(J) = Theta(b) Theta(z) Theta(b)^(-1) Theta(z)^(-1) = 1`.

### Proof of 2

Let `theta : G -> U(Q)`, `Q = prod_omega M_(d_n)`, be a homomorphism with `theta(b) != 1`, with unitary lifts
`theta_n(g) in U(d_n)`.

**A1 (shift the seed trace into [0,1)).** `B = theta(b)` is a unitary with `B^2 = 1`. So `B = B^*`, and
`B = p_+ - p_-` for complementary projections. Its trace `t = tau(p_+) - tau(p_-)` is real, and `t < 1` because
`p_- != 0` and `tau` is faithful. Put `theta^1_n(g) = theta_n(g) (+) I_(d_n) in U(2 d_n)`. These are lifts of the
homomorphism `theta (+) 1`, whose trace at `b` is

```text
s = (1 + t)/2  in  [0, 1).
```

**A2 (tensor powers).** For `k >= 1` put `W^(k)_n(g) = theta^1_n(g)^((x) k) in U((2 d_n)^k)`. By F1,

```text
||W^(k)_n(g) W^(k)_n(h) - W^(k)_n(gh)||_2 <= k ||theta^1_n(g) theta^1_n(h) - theta^1_n(gh)||_2,
tr W^(k)_n(g) = (tr theta^1_n(g))^k,
||W^(k)_n(b)^2 - I||_2 <= k ||theta^1_n(b)^2 - I||_2.
```

**A3 (diagonal choice).** Enumerate `G = {g_1, g_2, ...}` (repeating if `G` is finite). By F2, for each `k` choose
`n_k` so that `theta^1_(n_k)` has

```text
multiplicative defect < 1/k^2 on {g_1,...,g_k},
|tr theta^1_(n_k)(b) - s| < 1/k^2,        ||theta^1_(n_k)(b)^2 - I||_2 < 1/k^2.
```

The last condition is an `omega`-large condition because `theta^1(b)^2 = 1`. Put `V_k(g) = W^(k)_(n_k)(g)`, of
size `D_k = (2 d_(n_k))^k`, which is **even**. Using `|x^k - s^k| <= k |x - s|` for `|x|, |s| <= 1`,

```text
multiplicative defect of V_k on {g_1,...,g_k} < 1/k,
|tr V_k(b) - s^k| < 1/k,        ||V_k(b)^2 - I||_2 < 1/k.
```

Since `s^k -> 0`, F2 shows that for any nonprincipal `omega'` the classes `Theta_G(g) = [V_k(g)]` define a
homomorphism `Theta_G : G -> U(Q')`, `Q' = prod_(omega') M_(D_k)`, with `tau(Theta_G(b)) = 0`.

**A4 (exact balanced involution at every level).** Let `sgn(lambda) = 1` if `Re lambda >= 0` and `-1` otherwise,
for `|lambda| = 1`. Write `lambda = e^(i phi)` with `|phi| <= pi/2`. Then

```text
|lambda - 1| = 2|sin(phi/2)|,   |lambda^2 - 1| = 4|sin(phi/2)||cos(phi/2)| >= 2 sqrt(2) |sin(phi/2)|.
```

Applying this to `-lambda` when `Re lambda < 0` gives, for every unimodular `lambda`,

```text
|lambda - sgn(lambda)| <= |lambda^2 - 1|.
```

Let `B_k = sgn(V_k(b))`, by functional calculus for the normal matrix `V_k(b)`. It is a self-adjoint unitary, and
diagonalizing `V_k(b)` in an orthonormal basis gives

```text
||V_k(b) - B_k||_2 <= ||V_k(b)^2 - I||_2 < 1/k,
|tr B_k| <= |tr V_k(b)| + ||V_k(b) - B_k||_2 < s^k + 2/k,
```

where `|tr X| <= ||X||_2` is Cauchy--Schwarz for the normalized trace.

Let `p_+ + p_- = D_k` be the multiplicities of `+1` and `-1` for `B_k`. Then `p_+ - p_- = D_k - 2p_-` is even; put
`r_k = |p_+ - p_-|/2`. Change the sign of `r_k` orthonormal eigenvectors from the larger eigenspace. This gives a
self-adjoint unitary `B'_k` with both multiplicities `D_k/2`, and

```text
||B_k - B'_k||_2^2 = 4 r_k / D_k = 2 |tr B_k| < 2 (s^k + 2/k).
```

Hence `||V_k(b) - B'_k||_2 -> 0`, and `Theta_G(b) = [B'_k]` in `Q'`.

**A5 (the exact D8 partner).** In an orthonormal eigenbasis of `B'_k`, identify `C^(D_k) = C^(D_k/2) (x) C^2` with
`B'_k = I (x) diag(1,-1)`. Put `Z_k = I (x) [[0,1],[1,0]]`. Then

```text
Z_k^2 = I,     Z_k B'_k Z_k = -B'_k,     B'_k Z_k B'_k^(-1) Z_k^(-1) = -I.
```

Define `Theta` on the generators of `(CDS1)` by `Theta|_G = Theta_G`, `Theta(z) = [Z_k]` and `Theta(J) = -1`. We
check the relators.

- The relators of `G` hold because `Theta_G` is a homomorphism.
- `z^2 = 1` and `J^2 = 1` hold.
- `J` is central because `-1` is scalar.
- `Theta(b) Theta(z) Theta(b)^(-1) Theta(z)^(-1) = [B'_k Z_k B'_k Z_k] = -1 = Theta(J)`.

By the universal property of the presentation, `Theta` is a homomorphism `P(G,b) -> U(Q')` with `Theta(J) = -1`.
QED.

**Corollary A' (what the interface would prove).** Let `G = M rtimes A` be an actor--module base with involutive
seed `m_0`. If the uniform estimate `(ICR2)` of `infinite-character-interface-is-marked-radical-certificate`
holds for `P(G, m_0)`, then `J in Rad_hyp(P(G,m_0))`. By Lemma A this gives `m_0 in Rad_hyp(G)`, and hence the whole
normal closure of `m_0` in `G` lies in `Rad_hyp(G)`. For the SL3 coset lamp, this normal closure is the augmentation
submodule `L_0`; see Remark D3.

Conversely, `hyperlinear-radical-presentation-compactness` shows that `J in Rad_hyp(P(G,m_0))` gives a
non-effective finite-window modulus of the same qualitative form as `(ICR2)`, although not necessarily one that
factors through `E_act` and `eta_seed`. So the qualitative **terminal output** of the interface is equivalent to the element-level statement `m_0 in Rad_hyp(G)` about the unmarked base. This
refines `(CDS3)`. For `m_0 != 1`, membership forces `G` to be nonhyperlinear. It is a statement about the specific
element `m_0`, not only about the existence of some nontrivial radical element.

## 2. Lemma B: the dual-measure test for semidirect products

**Setting.** Let `M` be a countable abelian group, written additively. Let `A` be a countable group acting on `M` by
automorphisms `m -> a.m`, and put `G = M rtimes A` with

```text
(m,a)(m',a') = (m + a.m', a a'),        m = (m,1),   a = (0,a),   a m a^(-1) = a.m.
```

Let `M^ = Hom(M,T)` carry the dual action `(a.chi)(m) = chi(a^(-1).m)`. This is an action, since
`(a.(a'.chi))(m) = chi(a'^(-1) a^(-1).m)`, and `A` acts on the compact metrizable group `M^` by continuous
automorphisms. With `e_m(chi) = chi(m)`,

```text
e_m o (a^(-1).)  =  e_(a.m).                                        (B-dual)
```

For an `A`-invariant Borel probability measure `nu` on `M^`, let `N_nu = L^infinity(M^, nu) rtimes A` (F5), so that
`u_a f u_a^* = f o (a^(-1).)` and `u_a e_m u_a^* = e_(a.m)`. For `m_0 in M` put

```text
S_0 = {chi in M^ : chi(m_0) != 1}.
```

Define

```text
sigma_nu : G -> U(N_nu),       sigma_nu(m,a) = e_m u_a.
```

It is a homomorphism:

```text
e_m u_a e_(m') u_(a') = e_m (u_a e_(m') u_a^*) u_(aa') = e_(m + a.m') u_(aa').
```

By F5, `tau(sigma_nu(m,a)) = delta_(a,1) int e_m d nu`.

**Lemma B.**

- **(B1)** If some `A`-invariant `nu` has `nu(S_0) > 0` and `N_nu` is CE, then `m_0 notin Rad_hyp(G)` and `A` is
  hyperlinear.
- **(B2)** If `A` is hyperlinear and `m_0 notin Rad_hyp(G)`, then there is an `A`-invariant `nu` with `nu(S_0) > 0` and
  `N_nu` CE.

Consequently, for hyperlinear `A`, `m_0 in Rad_hyp(G)` iff every `A`-invariant probability measure on `M^` whose
crossed product is Connes embeddable is carried by the annihilator `m_0^perp = {chi : chi(m_0) = 1}`.

### Proof of (B1)

Let `iota : N_nu -> Q` be a trace-preserving embedding. Then `iota o sigma_nu : G -> U(Q)` is a homomorphism, and

```text
||iota(sigma_nu(m_0)) - 1||_2^2 = ||e_(m_0) - 1||_2^2 = int |chi(m_0) - 1|^2 d nu(chi) > 0,
```

since the integrand is positive on `S_0`. So `m_0 notin Rad_hyp(G)`.

The unitaries `u_a` satisfy `tau(u_a) = delta_(a,1)`, so `iota(u_a) != 1` for `a != 1`, and `A` is hyperlinear.

### Proof of (B2)

Let `theta : G -> U(Q)`, `Q = prod_omega M_(d_n)`, be a homomorphism with `theta(m_0) != 1`.

**Step 1 (invariant spectral measure).** Apply F3 to `theta|_M`. This gives `nu` on `M^` with
`int e_m d nu = phi(m) = tau(theta(m))`. For `a in A`,

```text
phi(a.m) = tau(theta(a) theta(m) theta(a)^(-1)) = phi(m),
```

while `int e_(a.m) d nu = int e_m o (a^(-1).) d nu = int e_m d((a^(-1).)_* nu)` by `(B-dual)`. By uniqueness in F3,
`(a^(-1).)_* nu = nu` for every `a`, so `nu` is `A`-invariant. Moreover `theta(m_0)^* = theta(-m_0)` gives

```text
int |chi(m_0) - 1|^2 d nu = 2 - phi(m_0) - phi(-m_0) = ||theta(m_0) - 1||_2^2 > 0,
```

so `nu(S_0) > 0`.

**Step 2 (a representation with the crossed-product trace).** Let `pi : G -> A`, `(m,a) -> a`, and let `alpha'` be
as in F7, with lifts `alpha'_j`. Enumerate `G = {g_1, g_2, ...}`. For each `l`, choose by F2 levels `n_l` and `j_l`
such that:

- `theta_(n_l)` has multiplicative defect and trace error below `1/l` on `{g_1,...,g_l}`;
- `alpha'_(j_l)` has the same on `{pi(g_1),...,pi(g_l)}`.

Put `rho_l(g) = theta_(n_l)(g) (x) alpha'_(j_l)(pi(g))`. By F1 its defect on `{g_1,...,g_l}` is below `2/l`, and

```text
tr rho_l(g) -> tau(theta(g)) . delta_(pi(g),1).
```

For `g = (m,a)`, this limit is `delta_(a,1) phi(m)`, because `|tau(theta(g))| <= 1`. By F2,
`rho = [rho_l] : G -> U(Q_rho)` is a homomorphism into a tracial matrix ultraproduct with

```text
tau(rho(m,a)) = delta_(a,1) phi(m) = tau_(N_nu)(sigma_nu(m,a)).
```

**Step 3 (transfer).** By F4, `W^*(sigma_nu(G))` is trace-preservingly isomorphic to `W^*(rho(G)) <= Q_rho`, so it is
CE.

**Step 4 (generation).** `W^*(sigma_nu(G))` contains `e_m = sigma_nu(m,1)` for all `m`. By Stone--Weierstrass (as in
F3) and F6, these generate `L^infinity(M^, nu)`. It also contains `u_a = sigma_nu(0,a)`. Hence
`W^*(sigma_nu(G)) = N_nu`, and `N_nu` is CE. QED.

**Remarks.**

1. For Haar measure `nu` the Fourier transform identifies `N_nu` with the group factor `L(G)`
   (`algebraic-envelope-principle`). Lemma B says that, for a single seed and hyperlinear `A`, one may replace the
   group factor by **any** invariant dual measure seeing the seed. The price is that `N_nu` must be CE.
2. No soficity, freeness or ergodicity of the dual action is used. The measure `nu` of Step 1 may be non-ergodic
   and non-free. Only `nu(S_0) > 0` matters.
3. Hyperlinearity of `A` enters only through F7. It is needed to kill the off-diagonal trace; otherwise `rho`
   would realize the trace of a non-regular representation of `A`.

## 3. Proposition C: coset-lamp seeds and fixed-algebra rigidity

**Setting.** Let `C <= A` be countable groups, `X = A/C`, `x_0 = C`. Put

```text
L = directSum_X F_2,    (d.l)(x) = l(d^(-1) x),    L_0 = {l : sum_x l(x) = 0},
m_a = delta_(x_0) + delta_(a x_0)    (a in A - C).
```

Both `L rtimes A` and its index-two subgroup `L_0 rtimes A` contain `m_a`.

**Proposition C.**

- **(C1)** Let `A` act by measure-preserving Borel automorphisms on a standard probability space `(Z, kappa)` with
  `L^infinity(Z) rtimes A` CE. Suppose a Borel set `E` has `kappa(cE triangle E) = 0` for all `c in C` and
  `kappa(aE triangle E) > 0`. Then `m_a notin Rad_hyp(L rtimes A)`.
- **(C2)** If `A` is hyperlinear and `m_a notin Rad_hyp(L rtimes A)`, then such `(Z, kappa, E)` exists. One may take
  `Z = F_2^X` with the coordinate shift and `E = {f : f(x_0) = 1}`.
- **(C3)** Let `H <= G` have index two and let `t in G - H` satisfy `t^2 = 1`. Then `Rad_hyp(H) = Rad_hyp(G) cap H`. In
  particular `Rad_hyp(L_0 rtimes A) = Rad_hyp(L rtimes A) cap (L_0 rtimes A)`, using `t = delta_(x_0)`.

Consequently, for hyperlinear `A` the following are equivalent:

1. `J in Rad_hyp(P(L rtimes A, m_a))`;
2. `m_a in Rad_hyp(L rtimes A)`;
3. `m_a in Rad_hyp(L_0 rtimes A)`;
4. `J in Rad_hyp(P(L_0 rtimes A, m_a))`;
5. **fixed-algebra rigidity:** for every p.m.p. action `A -> Aut(Z, kappa)` with CE crossed product,
   `L^infinity(Z)^C <= L^infinity(Z)^(<C,a>)`.

Here 1 iff 2 and 3 iff 4 are Lemma A, 2 iff 3 is (C3), and 2 iff 5 is (C1) and (C2). The step from sets to algebras in
5 holds because the abelian von Neumann algebra `L^infinity(Z)^C` is the norm-closed span of its projections
`1_E`. These are exactly the classes of `C`-invariant-mod-null sets, and the fixed algebra of `u_a` is norm closed.

### Proof of (C1)

**Exact invariance.** Put `E' = intersect_(c in C) cE`, a countable intersection. Then `c'E' = E'` exactly for
`c' in C`. Also `E - E' = union_c (E - cE)` is null, so `E' = E` mod null and
`kappa(aE' triangle E') = kappa(aE triangle E) > 0`, because `a` preserves `kappa`.

**Equivariant coloring.** Define `Phi : Z -> F_2^X` by

```text
Phi(z)(b x_0) = 1_(E')(b^(-1) z)        (b in A).
```

This is well defined: if `b' = bc` with `c in C`, then `1_(E')(c^(-1) b^(-1) z) = 1_(cE')(b^(-1) z) = 1_(E')(b^(-1) z)`.
Each coordinate is Borel, so `Phi` is Borel for the product structure (`X` countable). For `d in A` and
`x = b x_0`,

```text
Phi(dz)(x) = 1_(E')(b^(-1) d z) = Phi(z)(d^(-1) x),    so   Phi(dz) = d.Phi(z),  (d.f)(x) = f(d^(-1)x).
```

**Lamp unitaries.** For `l in L` put

```text
F_l(z) = (-1)^(sum_x l(x) Phi(z)(x)),
```

a finite sum. It is a Borel `{+1,-1}`-valued function, hence a self-adjoint unitary in `L^infinity(Z)`, with
`F_l F_(l') = F_(l+l')`. Since `Phi(d^(-1) z)(x) = Phi(z)(dx)`,

```text
F_l(d^(-1) z) = (-1)^(sum_x l(x) Phi(z)(dx)) = (-1)^(sum_y (d.l)(y) Phi(z)(y)) = F_(d.l)(z),
```

that is, `u_d F_l u_d^* = F_(d.l)`. Exactly as in Lemma B, `sigma_E(l,d) = F_l u_d` is a homomorphism
`L rtimes A -> U(L^infinity(Z) rtimes A)`. Now

```text
F_(m_a)(z) = (-1)^(1_(E')(z) + 1_(E')(a^(-1) z)) = (-1)^(1_(E')(z) + 1_(aE')(z)),
sigma_E(m_a) = 1 - 2 . 1_(E' triangle aE'),       ||sigma_E(m_a) - 1||_2^2 = 4 kappa(E' triangle aE') > 0.
```

Composing with a trace-preserving embedding into a tracial matrix ultraproduct gives a homomorphism not killing
`m_a`. QED.

### Proof of (C2)

Apply (B2) with `M = L` and `m_0 = m_a`. This gives an `A`-invariant `nu` on `L^` with `N_nu` CE and
`nu(chi(m_a) != 1) > 0`. The map `f -> chi_f`, `chi_f(l) = (-1)^(sum_x f(x) l(x))`, is a continuous group
isomorphism `F_2^X -> L^`, hence a homeomorphism. It intertwines the shift:

```text
(d.chi_f)(l) = chi_f(d^(-1).l) = (-1)^(sum_x f(x) l(dx)) = (-1)^(sum_y f(d^(-1)y) l(y)) = chi_(d.f)(l).
```

Transport `nu` to `F_2^X`; call it `kappa`. Let `E = {f : f(x_0) = 1}`.

- For `c in C`, `(c.f)(x_0) = f(c^(-1) x_0) = f(x_0)`, so `cE = E` exactly.
- `aE = {g : g(a x_0) = 1}`, since `(a.f)(a x_0) = f(x_0)`.
- `E triangle aE = {f : f(x_0) + f(a x_0) = 1} = {f : chi_f(m_a) = -1}`, which has positive measure.

The crossed product `L^infinity(F_2^X, kappa) rtimes A` is `N_nu`, which is CE. QED.

### Proof of (C3)

`Rad_hyp(H) <= Rad_hyp(G) cap H` holds by restriction. Conversely, let `h in H` and `theta : H -> U(Q)` with
`theta(h) != 1`. Since `H` is normal, `tkt in H` for `k in H`. Every element of `G` is uniquely `k` or `tk` with
`k in H`. In `M_2(Q)`, which is again a tracial matrix ultraproduct, put

```text
Pi(k) = diag(theta(k), theta(tkt)),     Pi(tk) = T Pi(k),     T = [[0,1],[1,0]].
```

Using `t^2 = 1`, `T^2 = 1` and `diag(x,y) T = T diag(y,x)`, we get `Pi(k) T = T Pi(tkt)`. The four product cases are:

```text
Pi(k)Pi(k')   = Pi(kk'),
Pi(k)Pi(tk')  = T Pi(tkt) Pi(k')   = T Pi(tkt k')  = Pi(t . tktk') = Pi(k t k'),
Pi(tk)Pi(k')  = T Pi(kk')          = Pi(t kk'),
Pi(tk)Pi(tk') = T T Pi(tkt) Pi(k') = Pi(tkt k').
```

These match the products `k.k'`, `k.tk'`, `tk.k'` and `tk.tk' = (tkt)k'` in `G`. So `Pi` is a homomorphism, and
`Pi(h) != 1`. QED.

**Remark C4 (profinite actions never separate).** Suppose every finite quotient `q : A -> Q` has `q(C) = q(A)`, as
for the SL3 pair. Let `(Z, kappa)` be an inverse limit of finite `A`-sets, with increasing `A`-invariant finite
partitions whose union generates the Borel sets. If `f in L^infinity(Z)^C`, the conditional expectations `E_i` onto
the finite levels are `A`-equivariant. So `E_i(f)` is `C`-invariant on a finite `A`-set, on which `A` acts through a
finite quotient with the same image as `C`. Hence `E_i(f)` is `A`-invariant. Since `E_i(f) -> f` in `L^2`, `f` is
`A`-invariant. Thus every separating action in (C1) must be genuinely non-profinite. This is the measure-theoretic
form of the finite-character exclusion in `sl3-codense-coset-lamp-recursive-host`.

**Remark C5 (Bernoulli instance).** For the uniform product measure on `F_2^X`, Fourier duality identifies
`N_nu` with `L(L rtimes A)` (`algebraic-envelope-principle`). Then (C1) specializes to: if `L rtimes A` is
hyperlinear, then `m_a notin Rad_hyp(L rtimes A)`, which is trivially true. The content of (C1) is that **any** CE
action with a `C`-invariant set moved by `a` suffices, including compact homogeneous ones.

## 4. Corollary D: the SL3 host under the open embeddability hypothesis (SH1)

**Setting.** Let

```text
A = SL_3(Z[1/2]),  C = SL_3(Z),  K = SL_3(Z_2),  L_2 = SL_3(Q_2),  h = diag(2,1,1/2),
X = A/C,  L = directSum_X F_2,  m_0 = delta_C + delta_(hC) = m_h,
P_host = P(L rtimes A, m_0),   P_host^0 = P(L_0 rtimes A, m_0).
```

These are the host of `sl3-codense-coset-lamp-recursive-host` and its augmentation variant; `h notin C`.

**Hypothesis (SH1 for Lambda').** `Lambda' < L_2` is a torsion-free cocompact lattice with `r >= 2` orbits of `K` on
`Y = L_2/Lambda'`, and `M = L^infinity(Y, mu) rtimes A` is Connes embeddable. This is the open claim
`sl3-homogeneous-quotient-crossed-product-is-connes-embeddable`.

**Corollary D.** Assume (SH1) for some such `Lambda'`.

- **(D1)** `m_0 notin Rad_hyp(L rtimes A)` and `m_0 notin Rad_hyp(L_0 rtimes A)`.
- **(D2)** `J notin Rad_hyp(P_host)` and `J notin Rad_hyp(P_host^0)`. There is a homomorphism into a tracial matrix
  ultraproduct sending `J` to `-1`.
- **(D3)** Fix any finite generating set of `P_host` (or `P_host^0`), any finite or countable enumeration of its
  relators, and a word `w_J` representing `J`. For every finite window `r_1,...,r_N` and every `delta > 0`, there
  are finite-dimensional unitary tuples `U` with `max_(j<=N) ||r_j(U) - I||_2 < delta` and
  `||w_J(U) - I||_2 > 2 - delta`. So no function `eta(delta) -> 0` can bound `||J(U) - I||_2` by any finite window's
  defect. The terminal estimate `(ICR2)` fails for this host, and so does every uniform actor word-energy interface
  whose output is `(ICR2)`.

*Proof of (D1).* By `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`, clauses 2 and 3 with
`n = 3`, `p = 2` and `S = {h}`, a `K`-orbit `P <= Y` has `U = 1 - 2 . 1_P` commuting with `u_C`, and
`W_h = U (U o h^(-1)) = 1 - 2 . 1_(P triangle hP)` is not scalar. Hence `mu(P triangle hP) > 0`. Since
`C <= K`, `cP = P` exactly for `c in C`.

Self-contained check of the last two facts. `P` is a `K`-orbit, hence compact and open, because `L_2 -> Y` is
open. If `mu(P triangle hP) = 0`, then the open set `hP - P` is null, and `mu` has full support, so `hP <= P`; by
symmetry `hP = P`. The stabilizer of the compact open set `P` is an open subgroup, by the tube lemma, and it contains
`<C,h> = A` (Remark D3). `A` is dense in `L_2`: its closure contains every `e_ij(x)`, `x in Q_2`, because `Z[1/2]` is
dense in `Q_2`, and these generate `SL_3(Q_2)`. An open subgroup is closed, so the stabilizer is `L_2`, and
transitivity gives `P = Y`, contradicting `r >= 2`.

Now apply (C1) with `(Z, kappa) = (Y, mu)`, `E = P` and `a = h`. The crossed product is `M`, CE by hypothesis. This
gives `m_0 notin Rad_hyp(L rtimes A)`, and (C3) gives the `L_0` statement.

*Proof of (D2).* Lemma A(2) applied to (D1).

*Proof of (D3).* Let `Theta` be as in (D2), into `Q' = prod_(omega') M_(D_k)`, and choose unitary lifts `U_k(s)` of
`Theta(s)` for the finitely many generators `s`. For each relator `r_j`, `||r_j(U_k) - I||_2 -> 0` along `omega'`.
Also `||w_J(U_k) - I||_2 -> ||Theta(J) - 1||_2 = 2`. Finitely many such conditions hold simultaneously on an
`omega'`-large set of `k`. This is the negation of clause 2 of `hyperlinear-radical-presentation-compactness` for
`w_J`, with any `epsilon < 2`. QED.

**Remark D3 (generation and the normal closure of the seed).** Since `h e_ij(x) h^(-1) = e_ij((h_i/h_j) x)` with
`(h_1,h_2,h_3) = (2,1,1/2)`,

```text
h^(-k) e_12(1) h^k = e_12(2^(-k)),   h^(-k) e_23(1) h^k = e_23(2^(-k)),   h^(-k) e_13(1) h^k = e_13(4^(-k)),
h^k e_21(1) h^(-k) = e_21(2^(-k)),   h^k e_32(1) h^(-k) = e_32(2^(-k)),   h^k e_31(1) h^(-k) = e_31(4^(-k)).
```

Taking integer powers (`e_ij(x)^n = e_ij(nx)`), `<C,h>` contains `e_ij(y)` for every `y in Z[1/2]` and `i != j`.
`Z[1/2]` is Euclidean with `N(2^k u) = |u|` for odd `u`: divide the integer numerator by the odd part of the divisor.
`SL_3` of a Euclidean ring is generated by elementary matrices (row reduction to a diagonal matrix of units, then
Whitehead's lemma). Hence `<C,h> = A`.

The graph on `X` with edges `{bC, bhC}` has connected component of `x_0` equal to `<C,h>/C = X`. Summing edge vectors
along paths gives every `delta_x + delta_y`. So the `F_2`-span of the `A`-orbit of `m_0`, and hence its normal
closure in `L rtimes A` intersected with `L`, is `L_0`.

**Remark D4 (the obstruction in contrapositive form; unconditional).** `A` is finitely generated and linear, hence
residually finite (Malcev), hence sofic and hyperlinear. So Proposition C's full equivalence applies to the SL3 pair.
Independently of (SH1), and without using hyperlinearity of `A`, (C1), (C3) and Lemma A give: **any** proof that
`J in Rad_hyp(P_host)`, and in particular any proof of the uniform interface for this host, proves that for
**every** p.m.p. action of `A` with CE crossed product,

```text
L^infinity(Z)^C  =  L^infinity(Z)^A.
```

Indeed a `C`-invariant set not fixed by all of `A = <C,h>` is moved by `h`. In particular it proves that (SH1) fails
for **every** torsion-free cocompact `Lambda'` with `r >= 2`: the interface is at least as strong as the non-embeddability
of this whole family of explicit crossed products. By Remark C4, profinite actions can never provide the
separation, so the rigidity statement has no finite-level content.

## 5. What is not claimed

- **(SH1) is not decided.** Corollary D is conditional. Remark D4 is its unconditional contrapositive. Nothing here
  shows that any `(SH1)` algebra is or is not CE.
- **Hyperlinearity of the SL3 lamp host is not decided.** If (SH1) holds, `P_host` may still be nonhyperlinear for
  reasons unrelated to the seed. What fails is the mechanism `interface -> J in Rad_hyp -> nonhyperlinear`.
- **The exact inequalities are untouched.** `(ISC3)` and `(ICR1)` are inequalities for exact spectral models and
  remain true. Only a uniform finite-window modulus `(ICR2)` for this host is excluded under (SH1).
- **Other hosts.** Proposition C applies to every countable pair `C <= A` with `A` hyperlinear. It gives no decision
  for the sharply two-transitive actor of `sharply-two-transitive-augmentation-lamp-host-audit`, whose own
  hyperlinearity is unaddressed here.
- **No novelty is claimed for Lemma B or F3--F7.** They are assembled from standard Gelfand, Riesz, GNS and
  ultraproduct arguments. No published source for Lemma B was located, and none is cited.
- **No sofic statement.** Proposition C concerns hyperlinear radicals and CE crossed products only. The sofic
  analogue, with sofic actions in place of CE crossed products, is not proved here.
