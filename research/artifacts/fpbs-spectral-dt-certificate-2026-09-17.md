# Spectral Duminil-Copin–Tassion certificates

September 17, 2026 (swarm-0917, worker w4-bs-wq-normal). Target hole:
`fpbs-amenable-wq-normal-relative-subcriticality`. Nothing here is refereed or
formally verified.

## 0. Summary

For a finite set `S` containing the identity, the Duminil-Copin–Tassion
exploration of the cluster inside `S` gives a finitely supported measure
`nu_{S,p}` on the group, carried by the outer boundary of `S`. Its total mass
is the DT quantity `phi_p(S)`. This note uses the **spectral radius** of
convolution by `nu_{S,p}` in place of its mass.

* **Theorem A.** If `sp(rho_Gamma(nu_{S,p})) < 1`, then
  `||T_p||_{2->2} <= |S| sum_k ||rho_Gamma(nu_{S,p})^k|| < infinity`. The
  condition is open in `p`, since `S` is fixed and the coefficients are
  polynomials in `p`. So a certificate at `p = p_c` gives `p_c < p_{2->2}`.
* **Theorem B.** For every subgroup `H`, if `sp(rho_{H\Gamma}(nu_{S,p})) < 1` on
  the Schreier space `l2(H\Gamma)`, then `chi^H_p = E_p|K_o ∩ H| < infinity`,
  and the same holds for all `p'` close to `p`.
* **Proposition C (the certificates are blind to the subgroup).** For every
  subgroup `H` and every nonnegative finitely supported `nu`,
  `sp_Gamma(nu) <= sp_{H\Gamma}(nu)`. Equality holds when `H` is amenable.

Consequences.

1. **A new decomposition of the target.** Relative subcriticality follows from
   the single finite-volume estimate at criticality, `p_c < p_sDT`. The
   threshold `p_sDT` is defined in Section 3.3. This bypasses the recorded death
   of "openness from criticality" (Section 4.4 of
   `relative-susceptibility-reduction.md`), because openness is now free.
2. **An obstruction to a class of approaches.** Relative certificates of this
   finite-exploration kind can never do better than absolute ones, by
   Proposition C. Any such certificate for `chi^H` is already a certificate for
   `p_c < p_{2->2}`. On this whole hierarchy, the amenable subgroup `H` gives no
   leverage. With `S = {o}` the hierarchy is exactly the classical bound
   `p d rho < 1` (Section 6.1). So the Kesten death of Attempt 4.1 ("count open
   walks") persists at every level of the hierarchy: the quotient operator has
   the same spectral radius as the full group operator.
3. **Sandwich.** `p_c <= p_sDT <= p_{2->2}`, and `{p : a certificate exists}`
   is the open interval `(0, p_sDT)`.

## 1. Setup

`Gamma` is a finitely generated group, `D` a finite symmetric generating set,
and `G = Cay(Gamma, D)` has edges `{x, xs}` (`s in D`, counted with
multiplicity). Left multiplication is a graph automorphism. Bernoulli bond
percolation `P_p`, `tau_p(x,y) = P_p(x <-> y)`, and `T_p` is the operator on
`l2(Gamma)` with kernel `tau_p`. `p_{2->2} = sup{p : ||T_p||_{2->2} < infinity}`.

For finite `S` containing `o = e`, write `o <->_S u` for a connection by open
edges with both endpoints in `S`. The oriented edge boundary `Delta S` is the set
of edges `{u,v}` with `u in S` and `v notin S`. Define

```text
nu_{S,p}(g) = p * sum_{ {u,v} in Delta S, v = g } P_p(o <->_S u),
```

a nonnegative measure supported in the outer vertex boundary of `S`. Its total
mass is the Duminil-Copin–Tassion quantity `phi_p(S)`. Each value
`P_p(o <->_S u)` is a polynomial in `p`, since it depends on finitely many edges.

For a set `X` with a right `Gamma`-action (`X = Gamma` or `X = H\Gamma`) and a
finitely supported `f`, put

```text
(rho_X(f) phi)(x) = sum_{g} f(g) phi(x g)        on l2(X).
```

Then `rho_X(f) rho_X(f') = rho_X(f * f')` and `rho_X(f)^* = rho_X(f^*)` with
`f^*(g) = f(g^(-1))`. Also `(rho_X(c) delta_x0)(x0) = c({g : x0 g = x0})`. Write
`sp_X(nu)` for the spectral radius of `rho_X(nu)`. For `X = Gamma`, `rho_Gamma`
is unitarily equivalent to the left regular representation `lambda_Gamma`, via
`phi -> phi(. ^(-1))`.

## 2. The exploration inequality in finite volume

**Lemma 2.1.** Let `Lambda` be a finite vertex set, and let
`tau^Lambda(x,y) = P_p(x <-> y inside Lambda)`, which is 0 unless
`x, y in Lambda`. For all `x, y`,

```text
tau^Lambda(x,y) <= 1[y in xS] + sum_g nu_{S,p}(g) tau^Lambda(xg, y).
```

*Proof.* If `x notin Lambda`, the left side is 0. Otherwise let `C` be the set
of vertices joined to `x` by open edges with both endpoints in
`xS ∩ Lambda`. If `y in C`, then `y in xS`. Suppose instead that `x <-> y`
inside `Lambda` but `y notin C`. Take an open path from `x` to `y` in
`Lambda`. Let `u` be its last vertex in `C`, and `v` the next vertex. If
`v in xS`, then `v in xS ∩ Lambda` and the edge `uv` is open with both endpoints
there, so `v in C`, which is a contradiction. So `{u,v} in Delta(xS)`, the edge
`uv` is open, and the rest of the path joins `v` to `y` inside `Lambda` using
no edge incident to `C`.

For a fixed set `A`, the event `{C = A}` depends only on edges incident to `A`,
and so does the state of `uv`, because `u in A`. The event "`v <-> y` inside
`Lambda` by edges not incident to `A`" depends only on edges not incident to
`A`. These are independent, so

```text
P(x <-> y in Lambda, y notin C)
  <= sum_{ {u,v} in Delta(xS) } sum_{A contains u} P(C = A) p tau^Lambda(v,y)
  <= sum_{ {u,v} in Delta(xS) } p P(x <->_{xS} u) tau^Lambda(v,y).
```

Left translation by `x^(-1)` maps `xS`, `Delta(xS)` and the connection events
to `S`, `Delta S` and `o <->_S x^(-1)u`. So the last sum is
`sum_g nu_{S,p}(g) tau^Lambda(xg, y)`. QED.

This is the DT exploration step, proved directly and in finite volume. No
statement of arXiv:1502.03050 is used in Theorems A and B, or in Proposition C.

## 3. Theorem A: certificates bound the connectivity operator

**Theorem A.** Let `S` be finite with `o in S`, and `R = rho_Gamma(nu_{S,p})`.
If `sp(R) < 1`, then entrywise

```text
tau_p(x,y) <= sum_{k >= 0} (R^k A_S)(x,y),      A_S(x,y) = 1[x^(-1) y in S],
```

and `||T_p||_{2->2} <= |S| sum_{k>=0} ||R^k|| < infinity`.

*Proof.* Fix a finite `Lambda`, and let `T^Lambda` have kernel `tau^Lambda`. The
kernel of `R` is `R(x,z) = nu(x^(-1) z)`. Lemma 2.1 says `T^Lambda <= A_S +
R T^Lambda` entrywise. All kernels are nonnegative, so iterating `m` times gives

```text
T^Lambda <= sum_{k<m} R^k A_S + R^m T^Lambda.
```

Here `(R^m T^Lambda)(x,y) = sum_g nu^{*m}(g) tau^Lambda(xg,y)
<= nu^{*m}(x^(-1) Lambda) = sum_{z in Lambda} <R^m delta_z, delta_x>`. This is at
most `|Lambda| ||R^m||`, and `||R^m||` tends to 0 because `sp(R) < 1` (Gelfand).
Let `m -> infinity`. Then let `Lambda` increase to `Gamma`, so that
`tau^Lambda -> tau_p` pointwise by monotone convergence of the events. This gives
the entrywise bound. For nonnegative kernels `0 <= K <= M` entrywise,
`||K|| <= ||M||`, because `|<K phi, psi>| <= <M|phi|, |psi|>`. Also
`||A_S|| <= |S|`, and `sum_k ||R^k||` converges since
`||R^k||^(1/k) -> sp(R) < 1`. QED.

**Corollary 3.1 (openness).** For fixed `S`, the set
`{p : sp(rho_Gamma(nu_{S,p})) < 1}` is open in `(0,1)`, and it is an interval
of the form `(0, p_S)` or empty.

*Proof.* `p -> rho(nu_{S,p})` is norm-continuous: finitely many group elements,
with polynomial coefficients. The spectral radius `sp(a) = inf_k ||a^k||^(1/k)`
is an infimum of continuous functions, hence upper semicontinuous, so the set
is open. Monotonicity: `nu_{S,p}` increases entrywise in `p`, so each kernel
`R^k` increases entrywise, so `||R^k||` increases, and so does `sp`. QED.

**3.3 The spectral DT threshold.** Define

```text
p_sDT(G) = sup{ p : there is a finite S containing o with sp(rho_Gamma(nu_{S,p})) < 1 }.
```

The set of such `p` is a union of open intervals starting at 0, so it equals
`(0, p_sDT)`. By Theorem A, `T_p` is bounded for `p < p_sDT`, so
`p_sDT <= p_{2->2}`. Since `sp(rho(nu)) <= ||rho(nu)|| <= nu(Gamma) = phi_p(S)`,
the DT criterion gives `p_sDT >= p_c`. This is Remark 3.2.

**Remark 3.2 (import used only for this lower bound).** Duminil-Copin–Tassion,
arXiv:1502.03050v3: `p_c = sup{p : phi_p(S) < 1 for some finite S containing o}`.
It is quoted verbatim, from TeX source lines 314–322 and 349–354, in
`research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md` Section 1, the
import of `fpbs-l2-gap-class-closed-under-local-limits-proof`. Nothing below
depends on this remark.

**Corollary 3.3.** If some finite `S` has `sp(rho_Gamma(nu_{S,p_c})) < 1`, then
`||T_{p_c}||_{2->2} < infinity` and `p_c < p_{2->2}`. Equivalently,
`p_c < p_sDT` implies `p_c < p_{2->2}`.

*Proof.* Corollary 3.1 applied at `p_c` gives an interval `(p_c - eps, p_c + eps)`
on which Theorem A applies. QED.

## 4. Theorem B: the relative certificate

**Theorem B.** Let `H <= Gamma` be any subgroup, `S` finite with `o in S`, and
`R_H = rho_{H\Gamma}(nu_{S,p})` on `l2(H\Gamma)`. If `sp(R_H) < 1`, then

```text
chi^H_p = sum_{h in H} tau_p(o,h) <= |S|^2 sum_{k >= 0} ||R_H^k|| < infinity,
```

and the same holds for every `p'` in an open interval containing `p`.

*Proof.* Fix a finite `Lambda` and put `sigma(x) = sum_{h in H} tau^Lambda(x,h)`.
Then `sigma <= |Lambda ∩ H|` and `sigma` vanishes off `Lambda`. Summing Lemma 2.1
over `y = h in H` gives

```text
sigma(x) <= f(x) + sum_g nu(g) sigma(xg),         f(x) = |xS ∩ H|.
```

Iterating, `sigma(o) <= sum_{k<m} sum_g nu^{*k}(g) f(g) + sum_g nu^{*m}(g) sigma(g)`.

* `f(hx) = |h(xS ∩ H)| = f(x)`, so `f` descends to `H\Gamma`. It is at most
  `|S|` and is supported on the at most `|S|` cosets `H s^(-1)`, `s in S`. Hence
  `sum_g nu^{*k}(g) f(g) = (R_H^k f)(H) <= |S| * |S| * ||R_H^k||`, using
  `(R_H^k delta_c)(H) = <R_H^k delta_c, delta_H> <= ||R_H^k||`.
* `sum_g nu^{*m}(g) sigma(g) <= |Lambda ∩ H| * nu^{*m}(Lambda)
  <= |Lambda ∩ H| * |H\H Lambda| * ||R_H^m||`, which tends to 0 as `m -> infinity`.

So `sigma(o) <= |S|^2 sum_k ||R_H^k||`, uniformly in `Lambda`. Monotone
convergence as `Lambda` increases to `Gamma` gives the bound on `chi^H_p`.
Openness is Corollary 3.1 with `rho_{H\Gamma}` in place of `rho_Gamma`; the same
proof applies. QED.

With `H = Gamma` the space `H\Gamma` is one point, `sp = nu(Gamma) = phi_p(S)`,
and Theorem B is the DT bound `chi_p < infinity` when `phi_p(S) < 1`. With
`H = {e}` it is a statement about `tau_p(o,o) = 1`, which is empty.

## 5. Proposition C: the certificates are blind to the subgroup

**Proposition C.** Let `nu >= 0` be finitely supported on `Gamma`, and `H` a
subgroup.

1. `||rho_Gamma(f)|| <= ||rho_{H\Gamma}(f)||` for every finitely supported
   `f >= 0`. Hence `sp_Gamma(nu) <= sp_{H\Gamma}(nu)`.
2. If `H` is amenable, `||rho_{H\Gamma}(f)|| <= ||rho_Gamma(f)||` for every
   finitely supported `f >= 0`. Hence `sp_{H\Gamma}(nu) = sp_Gamma(nu)`.

The spectral radius statements follow from the norm statements applied to
`f = nu^{*k}`, since `rho_X(nu)^k = rho_X(nu^{*k})`, and Gelfand's formula.

**Lemma 5.1 (faithful trace).** Let `b = rho_Gamma(c)` with `c = f^* * f`, and
`f` finitely supported. Then `||b|| = lim_k <b^k delta_e, delta_e>^(1/k)
= lim_k c^{*k}(e)^(1/k)`.

*Proof.* `b >= 0`. Let `m` be the spectral measure of `b` in the vector
`delta_e`. Clearly `<b^k delta_e, delta_e> <= ||b||^k`. Suppose
`m([||b|| - eps, ||b||]) = 0` for some `eps > 0`. Take continuous `g >= 0`
supported in `(||b|| - eps, ||b|| + eps)` with `g(||b||) = 1`. Then `x = g(b)` is
nonzero (because `||b||` lies in the spectrum), positive, and
`<x delta_e, delta_e> = 0`, so `x^(1/2) delta_e = 0`. The operator `x^(1/2)` is
a norm limit of polynomials in `b`, so it commutes with the left translations
`lambda(h)`, which commute with `rho`. Since `delta_h = lambda(h) delta_e`, this
gives `x^(1/2) = 0`, a contradiction. Hence every `eps` has
`m([||b|| - eps, ||b||]) > 0`, and
`<b^k delta_e, delta_e> >= (||b|| - eps)^k m([||b|| - eps, ||b||])`. Take
`k`-th roots. QED.

*Proof of C.1.* Let `c = f^* * f >= 0`. Then
`||rho_Gamma(f)||^2 = ||rho_Gamma(c)|| = lim c^{*k}(e)^(1/k)` by Lemma 5.1.
Since `c^{*k} >= 0` and `e in H`,

```text
c^{*k}(e) <= c^{*k}(H) = <rho_{H\Gamma}(c)^k delta_H, delta_H> <= ||rho_{H\Gamma}(c)||^k
          = ||rho_{H\Gamma}(f)||^(2k).
```

QED.

*Proof of C.2.* Choose a transversal `T` for `H\Gamma`, so every element is
uniquely `ht` with `h in H` and `t in T`. For `t in T` and `g in Gamma` write
`tg = c(t,g) t'`, with `c(t,g) in H` and `t' in T`. For nonnegative finitely
supported `phi, psi` on `H\Gamma` (functions on `T`) and finite `F` in `H`, put
`Phi(ht) = phi(t) 1_F(h)` and `Psi(ht) = psi(t) 1_F(h)`. Then

```text
<rho_Gamma(f) Phi, Psi> = sum_t psi(t) sum_g f(g) phi(Htg) |F ∩ F c(t,g)^(-1)|,
||Phi||^2 = |F| ||phi||^2,        ||Psi||^2 = |F| ||psi||^2.
```

The set `E = {c(t,g) : t in supp psi, g in supp f}` is finite. `H` is amenable,
so there is a finite `F` with `|F ∩ F c^(-1)| >= (1 - eps)|F|` for all `c in E`.
Take left Følner sets of `H` and invert them. Therefore
`(1 - eps) <rho_{H\Gamma}(f) phi, psi> <= ||rho_Gamma(f)|| ||phi|| ||psi||`. For
a nonnegative kernel the norm is the supremum over nonnegative finitely
supported unit vectors. QED.

**Corollary 5.2 (obstruction).** For every subgroup `H`, a relative certificate
`sp_{H\Gamma}(nu_{S,p}) < 1` implies the absolute certificate
`sp_Gamma(nu_{S,p}) < 1`. Hence it implies `||T_p||_{2->2} < infinity` for all
`p'` near `p`. For amenable `H` the two certificates coincide. So, on this
hierarchy of finite-volume spectral certificates, passing to the quotient by an
amenable wq-normal subgroup gains nothing:

* the invariant is `sp(rho(nu_{S,p}))`;
* the failing step is the hoped-for inequality `sp_{H\Gamma} < sp_Gamma`,
  refuted by C.1 and C.2.

Any proof of relative subcriticality through such certificates proves
`p_c < p_{2->2}` at the same time.

## 6. Calibration

### 6.1 `S = {o}` is the Benjamini–Schramm bound

`Delta{o}` consists of the `d = |D|` edges at `o`, and `P(o <->_{o} o) = 1`. So
`nu_{{o},p} = p * sum_{s in D} delta_s`, and `sp_Gamma = p d rho(G)`, with
`rho(G)` the spectral radius of simple random walk. The level-0 certificate is
`p d rho < 1`, the classical bound `p_u >= p_{2->2} >= 1/(d rho)`. For amenable
`H` its relative version has the same value `p d rho(Gamma/H)`. This is Kesten,
and it is exactly where Attempt 4.1 of the target died. Proposition C shows
that the same coincidence holds at every level `S`.

### 6.2 Amenable groups

For amenable `Gamma`, `sp_Gamma(nu) = nu(Gamma) = phi_p(S)`. This is Kesten's
criterion for nonnegative measures, and C.2 with `H = Gamma`, `H\Gamma` one
point. The DT theorem gives `phi_{p_c}(S) >= 1` for every `S`, so no certificate
exists at `p_c`, consistent with `p_c = p_{2->2} = p_u` there.

### 6.3 The 3-regular tree at `p_c = 1/2`

Take `S = B_R`. Each outer boundary vertex `g in S_{R+1}` has one edge into `S`,
from the `u in S_R` on its geodesic, so `nu(g) = p * p^R = 2^(-(R+1))`, and
`|S_{R+1}| = 3 * 2^R`. The mass is `phi = 3/2` for every `R`. But `nu` is `3/2`
times the uniform measure on the sphere `S_{R+1}`, whose convolution norm on the
`(q+1)`-regular tree is the spherical function
`(1 + n (q-1)/(q+1)) q^(-n/2)` at `n = R+1`, `q = 2` (Figà-Talamanca–Nebbia; at
`n = 1` it is Kesten's `2 sqrt(q)/(q+1)`). The measure is symmetric, so
`sp = ||.||`. Hence

```text
sp(rho(nu_{B_R, 1/2})) = (3/2)(1 + (R+1)/3) 2^(-(R+1)/2)
                       = 1.25 (R = 1),  1.06 (R = 2),  0.875 (R = 3).
```

`S = B_3` is a critical certificate on `T_3`, while the DT mass stays at `3/2`
for every `R`. So the spectral radius strictly improves on the mass criterion.

For general `p`, the same computation gives
`sp(rho(nu_{B_R,p})) = (3/2)(1 + (R+1)/3)(sqrt(2) p)^(R+1)`. This is below 1 for
large `R` exactly when `p < 1/sqrt 2`. Also
`||T_p|| = sum_n p^n |S_n| (1 + n/3) 2^(-n/2)`, which is finite exactly when
`p < 1/sqrt 2`. So on `T_3`, `p_sDT = p_{2->2} = 1/sqrt 2`: balls already
realise the sharp threshold. The value of `p_sDT` on balls is a lower bound for
`p_sDT`, and Theorem A gives the matching upper bound.

## 7. What this does to the target

**Route.** Let `Gamma` be nonamenable, and `H` an infinite amenable wq-normal
subgroup, or any amenable subgroup. Suppose some finite `S` has
`sp_Gamma(nu_{S,p_c}) < 1`. Proposition C.2 gives
`sp_{H\Gamma}(nu_{S,p_c}) < 1`. Theorem B then gives `chi^H_p < infinity` for
`p` slightly above `p_c`, which is the target claim. So

```text
fpbs-amenable-wq-normal-relative-subcriticality
  <=  [p_c < p_sDT on every Cayley graph of the class]    (OPEN)
    + Theorem B + Proposition C                              (ESTABLISHED here)
```

**What changed.**

* **Openness is solved.** Attempt 4.4 died because the set of `p` where
  `chi^H_p` is finite had no evident openness. A finite-volume certificate is
  automatically open (Corollary 3.1), so only the critical estimate remains.
* **The remaining estimate is not relative.** By Proposition C it is a statement
  about `Gamma` alone. By Corollary 3.3 it implies
  `||T_{p_c}||_{2->2} < infinity`, the L2 boundedness conjecture
  (`fpbs-nonamenability-bounds-critical-connectivity-operator`) on that graph.
  So in this framework the amenable subgroup gives no leverage. This is a
  precise negative result about the whole family of finite-exploration spectral
  certificates, not about one choice of `S`.
* **The estimate is weaker than existing sufficient conditions.**
  `fpbs-critical-sphere-fibre-operator-below-one` asks for
  `||lambda_Q(sigma_{p_c} 1_{S_Q(R_0)})|| < 1` with the full critical two-point
  function over a hyperbolic quotient with rapid decay. Here
  `P(o <->_S u) <= tau_{p_c}(o,u)`, the spectral radius replaces the norm, and
  no hyperbolicity or rapid decay is used.

**Open converse.** Does `p_c < p_{2->2}` imply `p_c < p_sDT`? Equivalently, is
`p_sDT = p_{2->2}`? It holds on `T_3` (Section 6.3). A positive answer would make the certificate an exact
finite-volume characterisation of the L2 gap. It would also give a
semi-decision procedure for `p_c < p_{2->2}`, since the certificate is
checkable in finite volume given upper bounds on norms of powers. This is not
settled here. If `T_{p_c}` is bounded, `sum_u tau_{p_c}(o,u)^2 < infinity`.
But the naive bound `sp <= p d ||lambda(tau_{p_c} 1_{S_R})||` needs this sphere
operator to be small, not merely bounded.

## 8. Novelty caveat

The graph search (`bin/cairn search`, 2026-09-17) found no equivalent node.
Hutchcroft's L2 papers (arXiv:1804.10191, arXiv:1904.05804) were not re-read
line by line for this statement, so prior art for Theorem A is not ruled out.
The proofs above are self-contained and do not rely on it.

