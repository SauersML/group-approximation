# Finite-nuclear-dimension factors: comparison, divisibility and purity of A (x)_min B (2026-09-16)

Swarm lane on `stw99-problem-xcv-pure-tensor-permanence`.  This artifact holds the full proofs behind

- `nucdim-factor-transfers-m-comparison` (Theorem A),
- `nucdim-factor-transfers-bounded-divisibility` (Theorem B and Corollary B'),
- `pure-tensor-nucdim-no-pi-quotient-is-pure` (Theorem D),
- `pure-tensor-nucdim-factor-pure-iff-global-glimm` (Corollary E'),

together with the audit of the imported statements `sv26-bounded-divisibility-dimension-reduction` and
`sv26-global-glimm-gives-two-color-splitting`.  Section 11 lists the full trust surface.

Throughout, `A (x) B` is the minimal tensor product, `K` the compacts, `E~` the unitization, `M(E)` the multiplier
algebra, `her(q)` the closure of `qEq`.  For `a,b in E_+`, `a <~ b` means that there are `v_j in E` with
`v_j b v_j^* -> a`; `a ~ b` means both directions.  `Cu(E)=(E (x) K)_+/~` with the usual order and addition.
`x << y` is compact containment.  Standard facts about `Cu` used without comment: `[(a-eps)_+] << [a]`,
`[a]=sup_eps [(a-eps)_+]`, addition preserves `<<` and suprema (Coward--Elliott--Ivanescu, J. reine angew. Math.
623 (2008)).  For `a,b in E_+` the relation `a <~ b` in `E (x) K` holds iff it holds in `E` (Lemma 1.3).  If `E` is
stable, every element of `Cu(E)` is `[a']` with `a' in E_+`: identify `E` with `E_0 (x) K`, take isometries
`s_j in B(l^2)` with `sum_j s_j s_j^* = 1` strongly, and put `t_j = 1 (x) s_j in M(E)`, so `t_i^* t_j = delta_ij` and
`sum_j t_j t_j^* = 1` strictly.  The partial sums of `V = sum_j t_j (x) e_(1j)` converge strictly in `M(E (x) K)` (for
`x in E (x) K`, `||(V_n-V_k)x||^2 = ||x^*(1 (x) sum_(k<j<=n) e_jj)x|| -> 0` and `||x(V_n-V_k)||^2 =
||x((sum_(k<j<=n) t_jt_j^*) (x) e_11)x^*|| -> 0`), `V^*V = 1` and `VV^* = 1 (x) e_11`.  For `a in (E (x) K)_+`,
`VaV^* = a' (x) e_11` with `a' in E_+` and `a = V^*(a' (x) e_11)V`, so `a ~ a' (x) e_11` by Lemma 1.4(iii).

Definitions used (as in Seth--Vilalta arXiv:2602.14809v2, Def. 3.2 and Def. 4.2, and Antoine--Perera--Thiel--Vilalta
arXiv:2406.11052v3):

```text
x <=_s y                 iff (k+1)x <= k y for some k in N
m-comparison             x <=_s y_j (j=0..m)  ==>  x <= y_0+...+y_m
almost unperforated      0-comparison
almost divisible         x' << x, N>=1  ==>  exists y:  N y <= x,  x' <= (N+1) y
pure                     almost unperforated and almost divisible
```

## 1. Elementary Cuntz-comparison lemmas

**Lemma 1.1 (order gives subequivalence).**  If `0 <= p <= q` in `E`, then `p <~ q`.

*Proof.*  Put `x=p^(1/2)` and `u_n=x(q+1/n)^(-1/2)`, computed in `E~`; `u_n in E`.  Since `p<=q`,
`u_n^* u_n=(q+1/n)^(-1/2) p (q+1/n)^(-1/2) <= q(q+1/n)^(-1) <= 1`.  Moreover

```text
p - u_n q u_n^* = x (1 - q(q+1/n)^(-1)) x = (1/n) x (q+1/n)^(-1) x,
```

whose norm is `(1/n)||(q+1/n)^(-1/2) p (q+1/n)^(-1/2)|| <= 1/n`.  So `u_n q u_n^* -> p`.  QED

**Lemma 1.2 (Kirchberg--Rordam perturbation).**  If `a,b in E_+` and `||a-b||<eps`, there is a contraction `d`
with `(a-eps)_+ = d b d^*`; in particular `(a-eps)_+ <~ b`.  Consequently, if `(a-eps)_+ <~ b` for every `eps>0`,
then `a <~ b`.

*Source.*  Kirchberg--Rordam, Adv. Math. 167 (2002), Lemma 2.2 (import; also Seth--Vilalta Lemma 2.3(iv)).  The
consequence: given `eps`, pick `v` with `||v b v^* - (a-eps)_+||<eps`; then `||v b v^*-a||<2eps`.

**Lemma 1.3 (compression).**  Let `P` be a projection in `M(F)` and `p,q in (PFP)_+`.  If `p <~ q` in `F`, then
`p <~ q` in `PFP`.  (Applied with `F=E (x) K` or `F=M_n(E)`, `P=1 (x) e_11` or `P=1_k`.)

*Proof.*  If `v_j q v_j^* -> p`, then `(P v_j P) q (P v_j P)^* = P v_j q v_j^* P -> PpP=p`, because `q=PqP`.  QED

**Lemma 1.4.**  (i) `a ~ a^2` for `a in E_+`.  (ii) For `z in E`, `z^*z ~ z z^*`.  (iii) If `z in E`, `x in M(E)`,
`q in E_+` and `r = x q x^*`, then `r <~ q`.

*Proof.*  (i) `a^2 <= ||a|| a` gives `a^2 <~ a` by Lemma 1.1; with `g(t)=((t-eps)_+)^(1/2)/t` we have
`(a-eps)_+ = g(a) a^2 g(a)`, so `a <~ a^2` by Lemma 1.2.  (ii) `(z^*z)^2 = z^*(zz^*)z <~ zz^*` by definition, and
`z^*z ~ (z^*z)^2` by (i); by symmetry `zz^* <~ z^*z`.  (iii) With `z=xq^(1/2) in E`, `r=zz^* ~ z^*z =
q^(1/2)x^*xq^(1/2) <= ||x||^2 q`; use Lemma 1.1.  QED

**Lemma 1.5 (hereditary subalgebras).**  If `p in her(q)_+`, then `p <~ q`.

*Proof.*  Let `e_n = g_n(q)`, `g_n(t)=min(1,nt)`.  Since `||g_n(q) q - q|| <= 1/n`, `e_n z -> z` and `z e_n -> z` for
`z in qEq`, hence for `z in her(q)`; thus `e_n p e_n -> p`.  Now `e_n p e_n <= ||p|| e_n^2 <= ||p|| n q`, because
`g_n(t)^2 <= g_n(t) <= nt`.  Lemma 1.1 gives `e_n p e_n <~ q`, and Lemma 1.2 gives `p <~ q`.  QED

**Lemma 1.6 (subequivalence from an operator inequality).**  Let `x=x^*` in `E~` with `x_+ in E`, and `c in E_+`
with `x <= c`.  Then `x_+ <~ c`.

*Proof.*  Fix `delta>0`.  Let `g_delta` be continuous on `R`, `0` on `(-inf,delta]`, `t^(-1/2)` on `[2delta,inf)`,
linear on `[delta,2delta]`.  Put `y=g_delta(x)`; since `g_delta` vanishes on `(-inf,delta]`, `y=g_delta(x_+) in E`.
Let `h(t)=t g_delta(t)^2 >= 0`.  Then `h(x) = y x y <= y c y`, and `y c y = (yc^(1/2))(yc^(1/2))^* ~ c^(1/2)y^2c^(1/2)
<= ||y||^2 c` (Lemma 1.4(ii) and 1.1), so `h(x) <~ c`.  On the spectrum of `x`, `(t-2delta)_+ <= ||x|| h(t)` (for
`t>=2delta` we have `h(t)=1` and `t<=||x||`; otherwise the left side is `0`).  Hence `(x_+-2delta)_+ = (x-2delta)_+
<~ h(x) <~ c`.  Let `delta -> 0` and use Lemma 1.2.  QED

**Lemma 1.7 (sums).**  For `p_0,...,p_m in E_+` and `eps_0,...,eps_m >= 0`:

```text
p_0+...+p_m  <~  p_0 (+) ... (+) p_m,          (sum_i p_i - sum_i eps_i)_+  <~  (+)_i (p_i - eps_i)_+ .
```

*Proof.*  For two terms let `R=(p^(1/2), q^(1/2))` (a `1x2` row).  Then `RR^* = p+q` and
`2(p (+) q) - R^*R = S^*S` with `S=(p^(1/2), -q^(1/2))`, so `R^*R <= 2(p (+) q)`; Lemma 1.4(ii) and 1.1 give
`p+q <~ p (+) q`; induct.  For the second statement, `p_i - eps_i <= (p_i-eps_i)_+`, so
`sum p_i - sum eps_i <= sum (p_i-eps_i)_+`; apply Lemma 1.6 and then the first statement.  QED

**Lemma 1.8 (perturbation with a threshold).**  If `||a-b|| < eps'` and `lambda >= 0`, then
`(a-lambda-eps')_+ <~ (b-lambda)_+`.

*Proof.*  `a - lambda - eps' <= b - lambda <= (b-lambda)_+`; apply Lemma 1.6.  QED

**Lemma 1.9 (support lemma).**  Let `E` be a C*-algebra, `C` a commutative unital C*-subalgebra of `M(E)`, and
`p,q in C cap E_+`.  Identify `C=C(Omega)`.  If `{p>0}` is contained in `{q>0}`, then `p <~ q`.

*Proof.*  Fix `delta>0`.  `K={p>=delta}` is compact and contained in `{q>0}`, so `kappa := min_K q > 0` (if `K` is
empty, `(p-delta)_+=0`).  Put `r = (p-delta)_+ / max(q,kappa) in C`, a positive element.  On `{p>delta}` we have
`q >= kappa`, so `rq=(p-delta)_+` there; off `{p>delta}` both vanish.  Hence `(p-delta)_+ = r^(1/2) q r^(1/2)`, and
Lemma 1.4(iii) with `x=r^(1/2) in M(E)` gives `(p-delta)_+ <~ q`.  Let `delta->0` (Lemma 1.2).  QED

**Lemma 1.10 (hereditary bound).**  If `b in E_+`, `delta>0` and `e in her((b-delta)_+)_+`, then
`e <= (||e||/delta) b`.

*Proof.*  Let `f(t)=min(1,t/delta)`.  Then `f(b)(b-delta)_+ = (b-delta)_+`, hence `f(b) z = z = z f(b)` for every
`z in her((b-delta)_+)`.  So `e = f(b) e f(b) <= ||e|| f(b)^2 <= ||e|| f(b) <= (||e||/delta) b`.  QED

**Lemma 1.11 (ideal membership).**  If `e` lies in the closed two-sided ideal of `E` generated by `d in E_+`, then
`[e] <= infinity[d] := sup_n n[d]` in `Cu(E)`.

*Proof.*  Fix `eps>0`.  The algebraic span of `E d E` is dense in the ideal, so there is `w = sum_(j=1)^n a_j d b_j`
with `a_j,b_j in E` and `||w w^* - e|| < eps` (approximate `e^(1/2)`).  Write `w = R . Col` with the row
`R=(a_1 d^(1/2),...,a_n d^(1/2))` and the column `Col=(d^(1/2)b_1,...,d^(1/2)b_n)^T`.  Then
`ww^* = R (Col Col^*) R^* <= ||Col||^2 R R^* ~ ||Col||^2 R^*R`, and `R^*R = D (a_i^* a_j)_(i,j) D` with
`D = d^(1/2) (x) 1_n`; since `(a_i^*a_j) <= ||(a_1,...,a_n)||^2 1_n`, `R^*R <= const . (d (x) 1_n)`.  By Lemmas 1.1,
1.4 and 1.2, `[(e-eps)_+] <= [ww^*] <= n[d] <= infinity[d]`.  Let `eps -> 0`.  QED

## 2. Order zero toolkit

A c.p.c. map `theta: D -> G` has **order zero** if `theta(a)theta(b)=0` whenever `a,b in D_+` and `ab=0`.
Imports from Winter--Zacharias, *Completely positive maps of order zero*, Munster J. Math. 2 (2009) 311--324,
arXiv:0903.3290 (numbering as compiled from the arXiv source, whose introduction is Section 0):

- **[WZ-oz 2.3] Structure theorem.**  If `theta` is c.p.c. order zero and `C=C^*(theta(D))`, there are a positive
  contraction `h in M(C) cap C'` and a *-homomorphism `pi: D -> M(C) cap {h}'` with `theta(x) = h pi(x)`.
- **[WZ-oz 3.2] Functional calculus.**  For positive `f in C_0((0,1])`, `f(theta)(x) := f(h)pi(x)` is a c.p. order
  zero map `D -> C`, contractive if `||f|| <= 1`.
- **[WZ-oz 3.3] Tensor products.**  Minimal tensor products of c.p.c. order zero maps are order zero; in particular
  amplifications `theta^(k)` and `id (x) theta` are order zero.
- **[WZ-oz 3.5] Cuntz comparison.**  If `a,b in M_k(D)_+` and `a <~ b`, then `theta^(k)(a) <~ theta^(k)(b)`;
  orthogonal elements go to orthogonal elements, so `theta^(k)(a (+) b) = theta^(k)(a) (+) theta^(k)(b)`.

**Lemma 2.1 (trilinear identity).**  A c.p.c. map `theta` has order zero iff
`theta(xy)theta(z) = theta(x)theta(yz)` for all `x,y,z in D`.

*Proof.*  If `theta` is order zero, write `theta = h pi` as in [WZ-oz 2.3]; as `h` commutes with `pi(D)`, both sides
equal `h^2 pi(xyz)`.  Conversely, if `a,b in D_+` and `ab=0`, then `a^(1/2)b=0` and
`theta(a)theta(b)=theta(a^(1/2)a^(1/2))theta(b)=theta(a^(1/2))theta(a^(1/2)b)=0`.  QED

**Lemma 2.2 (sequence algebras).**  Let `theta_k: D_k -> G_k` be c.p.c. maps and
`Theta: prod D_k/(+)D_k -> prod G_k/(+)G_k` the induced map.  (i) `Theta` is c.p.c.  (ii) If
`||theta_k(x_k y_k)theta_k(z_k) - theta_k(x_k)theta_k(y_k z_k)|| -> 0` for all bounded sequences, `Theta` is order
zero; in particular this holds if every `theta_k` is order zero.

*Proof.*  (i) The coordinatewise map is c.p.c. and maps `(+)D_k` into `(+)G_k`; positive elements of a quotient lift
to positive elements, and `M_n(prod/(+)) = prod M_n/(+) M_n`.  (ii) Lift `x,y,z`; the defect of the lifts is a
null sequence, so `Theta` satisfies the trilinear identity; use Lemma 2.1.  QED

## 3. Almost order zero approximations (import with audit)

**[WZ-dn 3.2]** (Winter--Zacharias, *The nuclear dimension of C\*-algebras*, Adv. Math. 224 (2010) 461--498,
arXiv:0903.4914, Proposition 3.2).  If `B` is separable and `dim_nuc B <= m`, there are finite-dimensional
`F_k = F_k^(0) (+) ... (+) F_k^(m)`, c.p.c. maps `psi_k: B -> F_k` and c.p. maps `phi_k: F_k -> B` whose restrictions
`phi_k^(i)` to `F_k^(i)` are c.p.c. order zero, such that `phi_k psi_k(b) -> b` for every `b in B`, and the induced map
`psibar: B -> prod F_k/(+)F_k` is order zero.  Writing `psi_k^(i)` for the compression of `psi_k` to `F_k^(i)`, each
`psibar^(i): B -> prod F_k^(i)/(+)F_k^(i)` is order zero (compression by a central projection).

Numbering and statement were checked against the arXiv source (`\label{almost-order-zero-approximation}`).  The
published statement says "almost contractive"; its separable-case proof constructs piecewise contractive
approximations (`psi` c.p.c., each `phi^(i)` c.p.c. order zero), which is the form used here.  Robert (Munster J.
Math. 4 (2011); arXiv:1002.2180, Proposition 1 and the proof of Theorem 1) uses exactly this consequence.

*Audit remarks on the published proof (the conclusion is unaffected).*  Re-deriving the separable case with the
paper's scheme (discard the blocks `j` of `Ftilde` on which `psitilde_j` fails to be almost order zero):

- the index set `I` should be defined with a strict inequality, or the case `||phitilde psitilde(c) phitilde
  psitilde(c')|| = 0` must be treated separately (it forces `phitilde_j(1)=0`);
- Proposition 3.1 of that paper is stated for norms `<= 1`, while `||phitilde psitilde(c)|| <= 1+eps`; rescaling
  gives `||phitilde_j(1)|| <= 2^(1/2) eps^(1/8)` for `j in I`;
- `||phitilde psitilde(c) phitilde psitilde(c') - cc'|| <= eps(1+eps)+eps < 3eps`, not `2eps`, giving
  `||psi(c)psi(c')|| <= 2^(1/2) eps^(1/8)`;
- the displayed estimate for `||b - phi psi(b)||` has a sign typo, and the sum over `I` is bounded by
  `(m+1)` times a maximum because blocks of one colour have orthogonal `phitilde_j(1)`;
- with `eps < (2(m+2))^(-16)` and target tolerance `t=eps^(1/16)` all estimates close;
- the sequence is built by testing a countable dense subset of the pairs `{(a,b): a,b positive contractions, ab=0}`
  together with a dense sequence of `B`; then `||psi_k(a)psi_k(b)|| -> 0` for all such pairs by approximation, and
  `phi_k psi_k -> id` pointwise by the uniform bound `||phi_k psi_k|| <= m+1`.

## 4. The sequence-algebra lemma

**Lemma P.**  Let `D_n` (`n in N`) be C*-algebras with almost unperforated `Cu(D_n)`, `Q = prod D_n/(+)D_n`, and
`x,y in M_N(Q)_+`.  If `(k+1)[x] <= k[y]` in `Cu(Q)` for some `k`, then `x <~ y` in `M_N(Q)`.

*Proof.*  Since `M_N(Q) = prod M_N(D_n)/(+)M_N(D_n)` and `Cu(M_N(D_n)) = Cu(D_n)`, assume `N=1`; rescale so that
`||x||,||y|| <= 1`.  Fix `eps>0`.  As `(k+1)[(x-eps)_+] << (k+1)[x] <= k[y] = sup_delta k[(y-delta)_+]`, there is
`delta>0` with `(k+1)[(x-eps)_+] <= k[(y-delta)_+]`, i.e. (Lemma 1.3) `(x-eps)_+ (x) 1_(k+1) <~ (y-delta)_+ (x) 1_k`
in `M_(k+1)(Q)`.  Pick `v in M_(k+1)(Q)` with `||v((y-delta)_+ (x) 1_k)v^* - (x-eps)_+ (x) 1_(k+1)|| < eps`.  Lift
`x,y` to positive contractions `(x_n),(y_n)` and `v` to a bounded `(v_n)`; functional calculus commutes with the
quotient map and the quotient norm is `limsup_n`, so there is `n_0` with

```text
|| v_n((y_n-delta)_+ (x) 1_k)v_n^* - (x_n-eps)_+ (x) 1_(k+1) || < eps        (n >= n_0).
```

By Lemma 1.2, `(k+1)[(x_n-2eps)_+] <= k[(y_n-delta)_+]` in `Cu(D_n)`; almost unperforation and Lemma 1.3 give
`(x_n-2eps)_+ <~ (y_n-delta)_+` in `D_n`.  Choose `u_n in D_n` with `||u_n (y_n-delta)_+ u_n^* - (x_n-2eps)_+|| < eps`
and, by Lemma 1.2, a contraction `d_n` with `(x_n-3eps)_+ = d_n u_n (y_n-delta)_+ u_n^* d_n^*`.  Put
`r_n = (y_n-delta)_+^(1/2) u_n^* d_n^* in D_n` for `n>=n_0` and `r_n=0` otherwise.  Then for `n>=n_0`

```text
r_n^* r_n = (x_n-3eps)_+ ,     r_n r_n^* in her((y_n-delta)_+),     ||r_n||^2 = ||(x_n-3eps)_+|| <= 1,
```

and Lemma 1.10 gives `r_n r_n^* <= (1/delta) y_n` for every `n`.  In `Q`, `r=[(r_n)]` satisfies `r^*r=(x-3eps)_+`
and `rr^* <= (1/delta)y`.  By Lemmas 1.4(ii) and 1.1, `(x-3eps)_+ <~ y`.  Let `eps -> 0` (Lemma 1.2).  QED

(This is the almost-unperforated analogue of Robert, arXiv:1002.2180, Lemma 2(ii) (`al-un`, stated there for
unperforated semigroups), whose proof it follows.)

**Lemma 4.1 (diagonal reflection).**  Let `E` be a C*-algebra, `E_infty = prod_k E/(+)_k E` and `iota` the diagonal
embedding.  If `a,b in M_N(E)_+` and `iota(a) <~ iota(b)` in `M_N(E_infty)`, then `[a] <= [b]`.

*Proof.*  Given `eps`, choose `v=[(v_k)]` with `||v iota(b) v^* - iota(a)|| < eps`; then `||v_k b v_k^* - a|| < eps`
for some `k`, and Lemma 1.2 gives `(a-eps)_+ <~ v_k b v_k^* <~ b`.  QED  (Robert, arXiv:1002.2180, Lemma 3, `iotalem`.)

## 5. Theorem A: a finite-nuclear-dimension factor transfers m-comparison

**Theorem A.**  Let `A` be a C*-algebra whose Cuntz semigroup is almost unperforated, and let `B` be a separable
C*-algebra with `dim_nuc B <= m`.  Then `Cu(A (x) B)` has `m`-comparison.

*Proof.*  Put `cA = A (x) K` and `E = cA (x) B`, so `(A (x) B) (x) K = E` and `E` is stable.  Take `(F_k,psi_k,phi_k)`
as in Section 3 and put, for `i=0,...,m`,

```text
Q^(i)   = prod_k (cA (x) F_k^(i)) / (+)_k (cA (x) F_k^(i)),       E_infty = prod_k E / (+)_k E,
Psi^(i): E -> Q^(i),        x |-> [ ((id (x) psi_k^(i))(x))_k ],
Phi^(i): Q^(i) -> E_infty,  [(x_k)] |-> [ ((id (x) phi_k^(i))(x_k))_k ].
```

*Step 1: `Psi^(i)` is c.p.c. order zero.*  It is c.p.c. (Lemma 2.2(i) applied to the coordinate maps composed with
the diagonal).  Let `P_k = id (x) psi_k^(i)` and `Def_k(x,y,z) = P_k(xy)P_k(z) - P_k(x)P_k(yz)`.  Each `Def_k` is
trilinear with `||Def_k(x,y,z)|| <= 2||x|| ||y|| ||z||`.  On elementary tensors,

```text
Def_k(a_1 (x) b_1, a_2 (x) b_2, a_3 (x) b_3) = a_1a_2a_3 (x) ( psi_k^(i)(b_1b_2)psi_k^(i)(b_3) - psi_k^(i)(b_1)psi_k^(i)(b_2b_3) ),
```

whose norm tends to `0` because `psibar^(i)` is order zero (Lemma 2.1 and the quotient norm).  By trilinearity the
defect tends to `0` on the algebraic tensor product and, by the uniform bound, on `E`.  Lemma 2.1 in `Q^(i)` shows
that `Psi^(i)` is order zero.

*Step 2: `Phi^(i)` is c.p.c. order zero.*  Each `id (x) phi_k^(i)` is c.p.c. order zero by [WZ-oz 3.3]; apply
Lemma 2.2.

*Step 3: `sum_i Phi^(i) Psi^(i) = iota`.*  The composite is `x |-> [((id (x) phi_k psi_k)(x))_k]`.  The maps
`id (x) phi_k psi_k` have norm at most `m+1` and converge pointwise to `id` on elementary tensors, hence on `E`.

*Step 4: comparison.*  Let `a, b_0,...,b_m in E_+` with `(k_i+1)[a] <= k_i[b_i]`.  Fix `i` and `k=k_i`.  By
Lemma 1.3, `a (x) 1_(k+1) <~ b_i (x) 1_k` in `M_(k+1)(E)`.  Applying the order zero amplification of `Psi^(i)`
([WZ-oz 3.3, 3.5]) gives `(k+1)[Psi^(i)(a)] <= k[Psi^(i)(b_i)]` in `Cu(Q^(i))`.  Every
`cA (x) F_k^(i)` is a finite direct sum of algebras `M_r(A (x) K)`, so its Cuntz semigroup is a finite product of
copies of `Cu(A)` and is almost unperforated.  Lemma P gives `Psi^(i)(a) <~ Psi^(i)(b_i)` in `Q^(i)`, and
[WZ-oz 3.5] for `Phi^(i)` gives

```text
Phi^(i)Psi^(i)(a) <~ Phi^(i)Psi^(i)(b_i) <= sum_l Phi^(l)Psi^(l)(b_i) = iota(b_i),
```

so `Phi^(i)Psi^(i)(a) <~ iota(b_i)` by Lemma 1.1.  By Step 3 and Lemma 1.7,

```text
iota(a) = sum_i Phi^(i)Psi^(i)(a) <~ (+)_i Phi^(i)Psi^(i)(a) <~ (+)_i iota(b_i)     in M_(m+1)(E_infty).
```

Lemma 4.1 (with `N=m+1`, `a (+) 0` and `(+)_i b_i`) yields `[a] <= [b_0]+...+[b_m]` in `Cu(E) = Cu(A (x) B)`.  QED

*Sanity checks.*  `A=C` is Robert's theorem (arXiv:1002.2180, Theorem 1; cited as Theorem 1.3 of the published
version by APTV).  `m=0` recovers almost
unperforation of `Cu(A (x) B)` for separable AF `B`.

## 6. Theorem B: a finite-nuclear-dimension factor transfers bounded divisibility

**Theorem B.**  Let `A` be a C*-algebra whose Cuntz semigroup is almost divisible, and let `B` be a C*-algebra with
`dim_nuc B <= m` (no separability needed).  For every `a in ((A (x) B) (x) K)_+`, `eps>0` and `N>=1` there is
`Y in Cu(A (x) B)` with

```text
[(a-eps)_+] <= (N+1) Y          and          N Y <= (m+1)[a].
```

*Proof.*  Keep `cA`, `E` as in Section 5.  Replacing `(a,eps)` by `(a/||a||, eps/||a||)` does not change the classes,
so assume `||a|| <= 1`.  Put

```text
eta = eps / (4(m+1)),        kappa = min(eta^2, eps/2).
```

*Approximation.*  Choose `a' = sum_l a_l (x) b_l` algebraic with `||a-a'|| < kappa/(3(m+2))` and a piecewise
contractive `m`-decomposable approximation `(F,psi,phi)` of `B` with `||phi psi(b_l) - b_l||` so small that
`T = id (x) phi psi` satisfies `||T(a)-a|| < kappa` (use `||T|| <= m+1`).  For `i=0,...,m` put

```text
D^(i) = cA (x) F^(i),    Psi_i = id (x) psi^(i): E -> D^(i),    theta_i = id (x) phi^(i): D^(i) -> E,
c_i = Psi_i(a),          T_i = theta_i Psi_i,                    T = T_0 + ... + T_m .
```

`c_i` is a positive contraction and `theta_i` is c.p.c. order zero ([WZ-oz 3.3]).  Write `theta_i = h_i pi_i` on
`C_i = C^*(theta_i(D^(i)))` ([WZ-oz 2.3]) and put `s=h_i`, `t=pi_i(c_i)`: commuting positive contractions in
`M(C_i)` with `T_i(a) = st in C_i`.  Let `theta_(i,eta) = (theta_i - eta)_+`, i.e. `x |-> (h_i-eta)_+ pi_i(x)`, a
c.p.c. order zero map `D^(i) -> C_i` ([WZ-oz 3.2]).

*Division in the first factor.*  `D^(i)` is stable and `Cu(D^(i))` is a finite product of copies of `Cu(A)`, hence
almost divisible.  Applying almost divisibility to `[(c_i-2eta)_+] << [(c_i-eta)_+]` gives `w_i in D^(i)_+` with

```text
N[w_i] <= [(c_i-eta)_+],          [(c_i-2eta)_+] <= (N+1)[w_i].
```

Put `Y_i = [theta_(i,eta)(w_i)]` and `Y = Y_0 + ... + Y_m`.  Applying amplifications of `theta_(i,eta)` to the two
relations (Lemma 1.3, [WZ-oz 3.3, 3.5]):

```text
N Y_i <= [theta_(i,eta)((c_i-eta)_+)] = [(s-eta)_+ (t-eta)_+],
[theta_(i,eta)((c_i-2eta)_+)] = [(s-eta)_+ (t-2eta)_+] <= (N+1) Y_i .
```

(`pi_i` is a *-homomorphism, so `pi_i((c_i-eta)_+) = (t-eta)_+`.)

*Upper bound.*  In the commutative algebra `C^*(1,s,t) in M(C_i)`, both `(s-eta)_+(t-eta)_+` and `(st-eta^2)_+` lie
in `C_i`, and `{s>eta, t>eta}` is contained in `{st>eta^2}`.  Lemma 1.9 gives
`(s-eta)_+(t-eta)_+ <~ (T_i(a)-eta^2)_+`.  Next, `T_i(a) <= T(a)` and `T(a) <= a + kappa` in `E~`, so
`T_i(a) - kappa <= a`; Lemma 1.6 gives `(T_i(a)-kappa)_+ <~ a`, and `(T_i(a)-eta^2)_+ <= (T_i(a)-kappa)_+`
because `kappa <= eta^2`.  Hence `N Y_i <= [a]` and `N Y <= (m+1)[a]`.

*Lower bound.*  By Lemma 1.8 (with `b = T(a)`, `lambda = eps/2` and `eps' = eps/2`, allowed because
`||a-T(a)|| < kappa <= eps/2`) and Lemma 1.7 (with all `eps_i = eps/(2(m+1)) = 2eta`),

```text
[(a-eps)_+] <= [(T(a)-eps/2)_+] <= sum_i [(T_i(a)-2eta)_+] .
```

Since `s,t <= 1`, `st > 2eta` forces `s > 2eta > eta` and `t > 2eta`; so `{st>2eta}` is contained in
`{(s-eta)_+(t-2eta)_+ > 0}`, and Lemma 1.9 in `C_i` gives `(T_i(a)-2eta)_+ <~ (s-eta)_+(t-2eta)_+`.  Therefore
`[(a-eps)_+] <= sum_i (N+1)Y_i = (N+1)Y`.  QED

**Corollary B'.**  Under the hypotheses of Theorem B, for every `N>=1` and `x' << x` in `Cu(A (x) B)` there is `y`
with `x' << N y << 2(m+1) x`.

*Proof.*  Write `x=[a]` and choose `eps>0` with `x' <= [(a-3eps)_+]`.  If `N=1`, take `y=[(a-2eps)_+]`.  If `N>=2`,
apply Theorem B to `(a-eps)_+`, tolerance `eps` and `N-1`: there is `y` with `[(a-2eps)_+] <= N y` and
`(N-1)y <= (m+1)[(a-eps)_+]`.  Then `x' <= [(a-3eps)_+] << [(a-2eps)_+] <= Ny`, and
`Ny <= 2(N-1)y <= 2(m+1)[(a-eps)_+] << 2(m+1)[a]`.  QED

*Why the cut `(h_i-eta)_+` is needed.*  The naive estimate `theta_i(c) <~ a` for the full map fails for general
c.p. maps, and `theta_i((c_i-eta)_+) = s(t-eta)_+` has support `{s>0,t>eta}`, which is not inside `{st>eta^2}`.
Cutting `h_i` is what makes both bounds hold with the same `Y_i`.

## 7. Imported dimension reduction (Seth--Vilalta)

Source: Seth--Vilalta, arXiv:2602.14809v2 (v1 submitted 16 Feb 2026), source file
`CXA_pure.tex`; statements checked against the source on 2026-09-16.  It is a preprint (not refereed as far as we
could verify).

**[SV 5.4] (`prp:RedandAmp`).**  If `Cu(D)` satisfies: for all `N>=1` and `x' << x` there is `y` with
`x' << Ny << Mx`, then with `M_1 = 2M^3`: for all `N>=1` and `x' << x = [f]` there is `c in her(f)_+` with
`[c] << x` and `x' << N[c] << M_1 x`.  We re-checked this proof (it uses only the refinement axioms O6, O7 via the
elementary Lemmas 5.2, 5.3 of that paper, and Lemma 2.3(i), i.e. Kirchberg--Rordam, Amer. J. Math. 122 (2000),
Prop. 2.7, as cited there); only routine `<<`-bookkeeping is left implicit.

**[SV 5.6] (`prp:Gen_DimRed`).**  If `D` has `m`-comparison and the divisibility hypothesis of [SV 5.4] with constant
`M`, then (i) Global Glimm Property, (ii) there is `L` such that every `x' << x` admits `y_0,y_1` with
`y_0+y_1 <= x` and `x' << L y_0, L y_1`, and (iii) purity are equivalent.

- (ii) => (iii).  SV cite an induction "as in the proof of" Antoine--Perera--Thiel--Vilalta arXiv:2406.11052v3,
  Lemma 6.3, then an `n`-almost-divisibility chain, then APTV Theorem 5.7.  We re-derive everything except the last
  import.

  *Claim (splitting into `l+1` pieces).*  If (ii) holds with constant `L`, then for every `l>=1` and `x' << x` there
  are `y_0,...,y_l` with `y_0+...+y_l <= x` and `x' << L^l y_j` for all `j`.  For `l=1` this is (ii).  Given `l` and
  `x' << x`, apply (ii): `u_0+u_1 <= x` and `x' << L u_0, L u_1`.  Interpolate `x' << x''' << L u_1`; as `u_1` is
  the supremum of a `<<`-increasing sequence `(w_n)` and addition preserves suprema, `x''' <= L w_n` for some `n`, so
  there is `w << u_1` with `x' << L w`.  The case `l` applied to `w << u_1` gives `v_0,...,v_l` with
  `v_0+...+v_l <= u_1` and `w << L^l v_j`.  Then `u_0+v_0+...+v_l <= x`, `x' << L u_0 <= L^(l+1) u_0` and
  `x' << L w <= L^(l+1) v_j`.  This is the case `l+1`.

  *`n`-almost divisibility.*  Let `M_1` be as in [SV 5.4], `L_1 = L^m`, `n = 2L_1M_1`, and fix `k>=1`, `x' << x`.
  [SV 5.4] with `N = 2kL_1M_1` gives `z` with `x' << N z << M_1 x`.  Choose `z' << z` with `x' << N z'` (as above)
  and then `x'' << x` with `N z' << M_1 x''` (possible since `N z' << N z << M_1 x = sup_p M_1 x_p` for a
  `<<`-increasing sequence `x_p` with supremum `x`).  The Claim for `x'' << x` and `l = m` gives `y_0,...,y_m` with
  `sum_j y_j <= x` and `x'' << L_1 y_j`.  For each `j`,

  ```text
  (L_1M_1 + 1)(k z')  <=  2kL_1M_1 z'  <=  M_1 x''  <=  L_1M_1 y_j ,
  ```

  i.e. `k z' <=_s y_j`.  By `m`-comparison `k z' <= y_0+...+y_m <= x`, and
  `x' << 2kL_1M_1 z' <= (k+1)(2L_1M_1+1) z' = (k+1)(n+1) z'`.  So `Cu(D)` is `n`-almost divisible in the sense of
  APTV Definition 4.1 (for all `x' << x` and `k>=1` there is `y` with `ky <= x` and `x' <= (k+1)(n+1)y`).  Together
  with `m`-comparison, `D` is `(m,n)`-pure (APTV Definition 5.1).

  *Import.*  APTV Theorem 5.7 (`prp:PureMain`, statement checked against the arXiv source): a C*-algebra is pure iff
  it is `(m,n)`-pure for some `m,n`.  This is the only load-bearing external step of (ii) => (iii) besides [SV 5.4].
- (iii) => (i): almost divisibility with `N=2` gives, for `x' << x`, some `y` with `2y <= x` and `x' <= 3y`, i.e.
  `(2,omega)`-divisibility; this is the Global Glimm Property by Thiel--Vilalta arXiv:2204.13059, Theorem 3.6 (import,
  as quoted in SV Paragraph 5.5).
- (i) => (ii): SV give this only as a list of modifications of APTV Lemma 6.2 (separable reduction through
  Thiel--Vilalta DimCu2 Prop. 6.1, then Robert Lemma 1).  This is the least detailed import and is kept as a
  separate claim, `sv26-global-glimm-gives-two-color-splitting`, so that Theorem D does not depend on it.

## 8. Theorem D: purity when no quotient has a compact properly infinite class

**Theorem D.**  Let `A` be pure and `B` separable with `dim_nuc B <= m`.  Put `C = A (x) B`.  Suppose that for every
closed ideal `J` of `C`, `Cu(C/J)` contains no nonzero compact properly infinite element (`z << z` and `2z <= z`).
Then `C` is pure.

*Proof.*  By Theorem A, `C` has `m`-comparison; by Corollary B', `C` satisfies the divisibility hypothesis of
[SV 5.4] with `M = 2(m+1)`.  Let `M_1 = 2M^3` and `L = max{2M_1, 3(m+1)}`.  We verify (ii) of [SV 5.6]; then
[SV 5.6] (ii) => (iii) gives purity.  This follows Seth--Vilalta's proof of their Proposition 5.10 for `C(X,A)`,
with evaluation at points replaced by the quotient map of `C` itself.  Work in `cC = C (x) K`, which is stable.

(a) *Reduction.*  Given `x' << x = [f]`, pick `eps` with `x' <= [(f-2eps)_+]`.  It suffices to find `y_0,y_1` with
`y_0+y_1 <= [f]` and `[(f-eps)_+] <= L y_0, L y_1`, since then `x' << [(f-eps)_+] <= Ly_j`.

(b) *Reduction and amplification.*  [SV 5.4] with `N = 2M_1` and `[(f-eps/2)_+] << [f]` gives `c in her(f)_+` with
`[(f-eps/2)_+] << 2M_1[c] << M_1[f]`.  Choose `delta>0` with `[(f-eps)_+] <= 2M_1[(c-delta)_+]`.

(c) *Two orthogonal pieces.*  Let `g_delta` be `0` on `[0,delta/2]`, `1` on `[delta,infty)`, linear between, and

```text
d0 = g_delta(c),        e = g_(delta/2)(c),        d1 = (1-e)^(1/2) f (1-e)^(1/2).
```

Since `g_delta(t)(1-g_(delta/2)(t)) = 0`, `d0 d1 = 0 = d1 d0`.  Both lie in `her(f)`: `d0 in C^*(c)`, and
`(1-e)^(1/2) = 1 - w` with `w in C^*(c)`, so `d1 = f - wf - fw + wfw`.  Put `y_0 = [d0]`, `y_1 = [d1]`.  With the
row `R = (d0^(1/2), d1^(1/2))` we have `RR^* = d0+d1` and, since `d0^(1/2)d1^(1/2) = 0`, `R^*R = d0 (+) d1`; so
`y_0+y_1 = [d0 (+) d1] = [d0+d1] <= [f]` by Lemmas 1.4(ii) and 1.5.

(d) `(c-delta)_+ <= ||c|| g_delta(c)`, so `[(f-eps)_+] <= 2M_1[d0] <= L y_0`.

(e) `f = f^(1/2) e f^(1/2) + f^(1/2)(1-e) f^(1/2)`.  The first summand is `~ e^(1/2) f e^(1/2) <= ||f|| e`, the
second is `~ d1` (Lemma 1.4(ii) with `z = f^(1/2)(1-e)^(1/2) in cC`).  By Lemma 1.7, `[f] <= [e] + [d1]`.

(f) `e <= (4/delta)(c-delta/4)_+`, so `[e] <= [(c-delta/4)_+] << [c] <= [f]`.  As
`2M_1[(c-delta/4)_+] << 2M_1[c] << M_1[f] = sup M_1[(f-epsbar)_+]`, there is `epsbar>0` with
`2M_1[e] <= M_1[(f-epsbar)_+]`.

(g) From (e) and (f): `2M_1[f] <= M_1[(f-epsbar)_+] + 2M_1[d1]`.

(h) *Quotient step.*  Let `I` be the closed ideal of `cC` generated by `d1` and `pi: cC -> cC/I`.  Put
`J = {c in C : c (x) e_11 in I}`, a closed ideal of `C`.  Closed ideals are invariant under multipliers (for `mu in
M(cC)`, `x in I` and an approximate unit `u_lambda` of `cC`, `mu x = lim (mu u_lambda) x in I`).  Hence for `c in J`,
`c (x) e_ij = (1 (x) e_i1)(c (x) e_11)(1 (x) e_1j) in I`, and these span a dense subspace of `J (x) K` inside
`C (x) K`; so `J (x) K` is contained in `I`.  Conversely, for `x in I` the slice `x_ij in C` defined by
`(1 (x) e_1i) x (1 (x) e_j1) = x_ij (x) e_11` (true on elementary tensors, hence everywhere) lies in `J`, and with
`p_n = sum_(i<=n) e_ii`, `x = lim_n (1 (x) p_n) x (1 (x) p_n) = lim_n sum_(i,j<=n) x_ij (x) e_ij in J (x) K`.  Thus
`I = J (x) K`, and since `K` is nuclear, `cC/I = (C (x) K)/(J (x) K) = (C/J) (x) K`, so `Cu(cC/I) = Cu(C/J)`.
Applying `pi` to (g) (a *-homomorphism induces an order-preserving additive map on `Cu`, with `[pi d1] = 0` and
`pi((f-epsbar)_+) = (pi f - epsbar)_+`),
`2M_1[pi f] <= M_1[(pi f - epsbar)_+] << M_1[pi f]`.  So `z = M_1[pi f]` satisfies `2z << z`, hence `z << z` and
`2z <= z`: a compact properly infinite element.  By hypothesis `z = 0`, so `pi(f) = 0` and `f in I`.

(i) By Lemma 1.11, `[f] <= infinity[d1]`.  Since `[(c-delta/4)_+] << [f]`, there is `n` with
`[(c-delta/4)_+] <= n[d1]`, and by (e), (f): `[f] <= (n+1)[d1]`.

(j) *Traces.*  Let `tau` be any lower semicontinuous `[0,infty]`-valued 2-quasitrace and `d_tau` its dimension
function (additive, order preserving).  From (g), `2M_1 d_tau(f) <= M_1 d_tau(f) + 2M_1 d_tau(d1)`.  If
`d_tau(f) < infty`, then `d_tau(f) <= 2 d_tau(d1)`; if `d_tau(f) = infty`, then `d_tau(d1) = infty` by (i).  In both
cases `d_tau(f) <= (2/3) d_tau(3[d1])`.

(k) Robert, Munster J. Math. 4 (2011), Lemma 1 (`m`-comparison is equivalent to: `[a] <_tau [b_i]` for all
`i=0..m` implies `[a] <= sum [b_i]`, where `<_tau` means `d_tau(a) <= (1-gamma)d_tau(b_i)` for all `tau` and some
`gamma>0`), applied with `b_i = 3[d1]` and `gamma = 1/3`, gives `[f] <= 3(m+1)[d1]`.  So
`[(f-eps)_+] <= [f] <= L y_1`.

This verifies (ii) with the constant `L = 32(m+1)^3`, and [SV 5.6] gives that `C` is pure.  QED

*Remarks.*  (1) For `B = C(X)` this is Seth--Vilalta Prop. 5.10 + Thm 5.6, with a hypothesis on quotients of
`C(X,A)` instead of `A`.  (2) Seth--Vilalta Theorem 6.7 covers ASH `B` under hypotheses on `A`; Theorem D allows any
separable `B` of finite nuclear dimension, but its hypothesis is on quotients of `A (x) B`, and we do not know how
to reduce it to conditions on `A` and `B` separately (quotients of `A (x)_min B` need not be tensor products unless
exactness conditions hold).

## 9. Corollary E' and the remaining gap

**Corollary E'.**  Let `A` be pure and `B` separable with `dim_nuc B <= m`.  Then `A (x) B` is pure iff it has the
Global Glimm Property, iff it satisfies (ii) of [SV 5.6].

*Proof.*  Theorem A and Corollary B' supply the hypotheses of [SV 5.6] for `A (x) B`; (i) => (ii) is
`sv26-global-glimm-gives-two-color-splitting`, (ii) => (iii) and (iii) => (i) are in
`sv26-bounded-divisibility-dimension-reduction`.  QED

Remaining gap (open hole `pure-tensor-nucdim-factor-has-global-glimm`): does `A (x) B` have the Global Glimm Property
for pure `A` and separable `B` of finite nuclear dimension?  By Theorem A and Corollary B', `A (x) B` satisfies the
hypotheses of [SV 5.6]; Seth--Vilalta remark after their Theorem 5.6 that such algebras are nowhere scattered (not
re-derived here).  So a positive answer to the Global Glimm Problem would finish the finite-nuclear-dimension case of
Problem XCV.  Known
Glimm-problem solutions do not apply directly: Thiel--Vilalta's results need ideal-lattice or (V)-type hypotheses,
and APTV Theorem 6.5 needs finite nuclear dimension of the algebra itself, which `A (x) B` need not have.

## 10. Failed shortcuts (recorded so they are not retried)

- Square-zero elements per colour: Theorem B produces divisions colour by colour, but a Glimm square-zero element
  for `A (x) B` would have to be assembled across colours, and the images of different colours overlap; no bound
  on the overlap was found.
- Applying Lemma 1.6 to the full map `id (x) phi^(i) psi^(i)` without the functional-calculus cut: false in general
  (see the remark after Corollary B').
- Using APTV Thm 6.5 directly: `A (x) B` need not have finite nuclear dimension.

## 11. Trust surface

Proved here in full: Lemmas 1.1, 1.3--1.11, 2.1, 2.2, P, 4.1; Theorems A, B, D modulo the imports below;
Corollaries B', E' modulo the imports below; the Claim and the `n`-almost-divisibility chain in the proof of
[SV 5.6] (ii) => (iii); the description of the ideals of `C (x) K`.

Published imports: Kirchberg--Rordam Adv. Math. 167 (2002) Lemma 2.2; Winter--Zacharias Munster J. Math. 2 (2009)
Thm 2.3, Cors 3.2, 3.3, 3.5 (arXiv numbering); Winter--Zacharias Adv. Math. 224 (2010) Prop. 3.2; Robert Munster J.
Math. 4 (2011) Lemma 1; Coward--Elliott--Ivanescu (2008) for the Cu axioms; exactness of `- (x) K`.

Preprint imports:

- used by Theorem D: Seth--Vilalta arXiv:2602.14809v2 Lemma 5.4 (proof re-checked, see Section 7) and
  Antoine--Perera--Thiel--Vilalta arXiv:2406.11052v3 Theorem 5.7 (`(m,n)`-pure implies pure);
- used additionally by Corollary E': Thiel--Vilalta arXiv:2204.13059 Theorem 3.6, and Seth--Vilalta Theorem 5.6
  (i) => (ii), which SV give only as modifications of APTV Lemma 6.2 (with Thiel--Vilalta DimCu2 Prop. 6.1 and
  Robert Lemma 1).

The referee should attack APTV Theorem 5.7 and [SV 5.4] first: they are the only steps of Theorem D not re-derived
here.  For Corollary E' the weakest link is the sketched SV Theorem 5.6 (i) => (ii).
