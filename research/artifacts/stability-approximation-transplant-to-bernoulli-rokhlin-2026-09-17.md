# Stability-approximation transplant to Bernoulli Rokhlin entropy (2026-09-17)

Agent a-gs-pull-9, role transplanter, family stability-approximation, target
`bernoulli-rokhlin-entropy-maximal-for-every-group` (INF).

The question: can sofic entropy, the only known source of lower bounds
`h^Rok(A^G) >= log|A|`, be transplanted from permutation models to unitary
(Hilbert--Schmidt) models, so that it reaches hyperlinear groups such as the
binary Leavitt unit group `U`, where the sofic-radical localization forces every
deficit to live (`sofic-radical-localizes-bernoulli-deficit-witnesses`,
`openai-leavitt-unit-nonsofic`)?

Answer recorded here: the natural transplant splits into three species. Each dies at
an identified step, and one precisely stated gate is left.

## 0. Dictionary

| sofic entropy | transplant |
| --- | --- |
| permutation model `sigma: G -> Sym(n)` | unitary model `sigma: G -> U(n)` |
| partition `x: [n] -> A` | commuting projections `(p_a)_(a in A)`, `sum_a p_a = 1` |
| pullback `x o sigma(g)` | translate `sigma(g) p_a sigma(g)^*` |
| empirical distribution of `F`-patterns | moments `tr_n(prod_(g in F) sigma(g) p_(w(g)) sigma(g)^*)` |
| Hamming pseudometric | `rho(p,p') = max_a ||p_a - p'_a||_2` (normalized HS) |
| `h_Sigma = sup_eps inf_(F,delta) limsup (1/n) log N_eps` | same formula, `n^(-beta)` normalization allowed |

**Definition (HS commutative microstates).** Let `G` be countably infinite, `A` finite,
`q=|A| >= 2`. For `sigma: G -> U(n)`, a finite `F` containing `e`, and `delta>0`,
`Mic(sigma,F,delta)` is the set of tuples `p=(p_a)_(a in A)` of projections in `M_n`
with `sum_a p_a = 1`, such that:

- the elements `sigma(g) p_a sigma(g)^*` (`g in F`, `a in A`) pairwise commute, and
- for every `w: F -> A`, `|tr_n(prod_(g in F) sigma(g) p_(w(g)) sigma(g)^*) - q^(-|F|)| < delta`.

Relaxing exact commutation to `||[.,.]||_2 < delta` only enlarges the set, so lower
bounds proved for the exact version hold for the relaxed version too. Define

```text
h^beta_Sigma(A) = sup_eps inf_(F,delta) limsup_j n_j^(-beta) log N_eps(Mic(sigma_j,F,delta), rho).
```

Diagonal projections under permutation models recover the sofic-entropy microstates:
Borel partitions of `[n]`. This is the transplant a stability-approximation worker
would first try.

## 1. Theorem K1: amplification makes the count base-blind (ESTABLISHED)

**Theorem K1.** Let `Sigma = (sigma_j: G -> U(d_j))` be any sequence such that for every
`(F,delta)`, `Mic(sigma_j,F,delta)` is nonempty for all large `j`. Fix `beta in [1,2)`.
Let `m_j` be even with `m_j^(2-beta)/d_j^beta -> infinity`. Then along the amplified models

```text
Sigma (x) 1 = (sigma_j (x) 1_(m_j): G -> U(d_j m_j))
```

we have `h^beta_(Sigma (x) 1)(A) = +infinity` for every finite `A` with `|A| >= 2`. In
fact the inner `limsup` is `+infinity` for every `eps < 1/(2000 q)` and every `(F,delta)`
with `delta < 1/(2q)`.

`Sigma (x) 1` is again an approximation: multiplicativity defects and normalized
traces are unchanged by `(x) 1_m`. If `sigma_j` are permutation matrices, `sigma_j (x) 1_m`
are permutation matrices, so `Sigma (x) 1` is a sofic approximation whenever `Sigma` is.

### Proof

Write `d=d_j`, `m=m_j=2M`, identify `M_(dm) = M_d (x) M_2 (x) M_M`, and put
`sigma~ = sigma (x) 1_2 (x) 1_M`. Fix `(F,delta)`, take `j` large, and take
`p in Mic(sigma_j,F,delta)`.

**Step 1 (swapped block microstate).** Fix letters `a0 != a1` and let `pi` be their
transposition. The uniform product measure is invariant under applying `pi` to all
coordinates, so the moment targets `q^(-|F|)` are invariant under `w -> pi o w`. Hence
`p^pi := (p_(pi a))_a` lies in `Mic(sigma_j,F,delta)`. Put

```text
P_a = p_a (x) e11 (x) 1_M + p_(pi a) (x) e22 (x) 1_M.
```

These are commuting projections summing to `1`. Their `sigma~`-translates commute
blockwise. Every moment is the average of the corresponding moments of `p` and `p^pi`,
so `P in Mic(sigma~,F,delta)`.

**Step 2 (commutant rotations).** For `X in M_M` put

```text
H(X) = 1_d (x) (e12 (x) X + e21 (x) X^*),    W(X) = exp(i H(X)).
```

`H(X)` is self-adjoint and commutes with `sigma~(G)`, so `W(X)` is a unitary in the
commutant of `sigma~(G)`. Conjugation by `W(X)` fixes every `sigma~(g)` and maps
commuting families to commuting families, so all the moments of
`(sigma~, W P W^*)` equal those of `(sigma~, P)`. Therefore
`W(X) P W(X)^* in Mic(sigma~,F,delta)`.

**Step 3 (exact first-order term).** With `p0=p_(a0)`, `p1=p_(a1)`, `P_(a0) = p0 (x) e11 + p1 (x) e22`.
A direct multiplication gives

```text
[H(X), P_(a0)] = (p1 - p0) (x) e12 (x) X + (p0 - p1) (x) e21 (x) X^*.
```

Since `p0 p1 = 0`, `(p1-p0)^2 = p0+p1`. Normalizing the trace on `M_(2dM)`,

```text
||[H(X),P_(a0)]||_2^2 = tau_d(p0+p1) tau_M(X^*X) = s^2 ||H(X)||_2^2,
s^2 := tau_d(p0+p1),    ||H(X)||_2^2 = tau_M(X^*X) = ||X||_(2,M)^2.
```

The map `X -> [H(X),P_(a0)]` is linear, so `||[H(X)-H(X'),P_(a0)]||_2 = s ||X-X'||_2`. The
moment condition with `F={e}` gives `|tau(p_a) - 1/q| < delta`, so `s^2 >= 2/q - 2 delta >= 1/q`
when `delta < 1/(2q)`. Also `s <= 1`.

**Step 4 (remainder).** Write `e^(iH) P e^(-iH) = P + i[H,P] + R(H)`, where
`R(H) = sum_(k>=2) (i^k/k!) ad_H^k(P)`. Let `||H||_inf, ||H'||_inf <= r` and `Delta = H-H'`.
Telescoping, `ad_H^k(P) - ad_(H')^k(P)` is a sum of `k` terms
`ad_H^i ad_Delta ad_(H')^(k-1-i)(P)`. We have:

- `||ad_(H')^(k-1-i)(P)||_inf <= (2r)^(k-1-i)`;
- `||[Delta,Y]||_2 <= 2||Y||_inf ||Delta||_2`;
- `||[H,Y]||_2 <= 2r ||Y||_2`.

So each term is at most `2(2r)^(k-1)||Delta||_2`, and

```text
||R(H)-R(H')||_2 <= sum_(k>=2) 2k(2r)^(k-1)/k! ||Delta||_2 = 2(e^(2r)-1) ||Delta||_2.
```

Take `r = s/10`. Since `s <= 1`, `2(e^(s/5)-1) <= 2 (s/5) e^(1/5) < 0.49 s`. Therefore

```text
||W(X)P_(a0)W(X)^* - W(X')P_(a0)W(X')^*||_2 >= (s - 0.49 s)||X-X'||_2 >= (s/2)||X-X'||_2      (K1a)
```

whenever `||X||_inf, ||X'||_inf <= r`.

**Step 5 (packing in the operator-norm ball).** Let `Z` be complex Ginibre in `M_M` with
independent entries, `E|Z_(ik)|^2 = 1/M`, and density `(M/pi)^(M^2) exp(-M Tr Z^*Z)`.

- *Norm bound.* Let `N` be a `1/4`-net of the unit sphere of `C^M` with `|N| <= 9^(2M)`.
  Then `||Z||_inf <= 2 max_(u,v in N) |<Zu,v>|`. Each `<Zu,v>` is complex Gaussian with
  variance `1/M`, so `P(|<Zu,v>| > 6) = e^(-36M)`. A union bound gives
  `P(||Z||_inf > 12) <= 81^(2M) e^(-36M) <= e^(-27M) <= 1/2`.
- *Small balls.* For every `Y`, a normalized-HS ball of radius `eta` around `Y` is a Euclidean
  ball of radius `sqrt(M) eta` in real dimension `2M^2`. Its Ginibre mass is at most

  ```text
  (M/pi)^(M^2) pi^(M^2) (M eta^2)^(M^2) / (M^2)! <= (e eta^2)^(M^2),
  ```

  using `(M^2)! >= (M^2/e)^(M^2)`.

Let `S` be a maximal `1/4`-separated set, in normalized HS, inside `{||Z||_inf <= 12}`. The
`1/4`-balls around `S` cover this set, so `1/2 <= |S| (e/16)^(M^2)` and
`|S| >= (1/2)(16/e)^(M^2)`. Rescale `X = (r/12) Z`, `Z in S`. Then `||X||_inf <= r`, and the
pairwise distances satisfy `||X-X'||_2 >= r/48`.

**Step 6 (count).** By `(K1a)`, the microstates `W(X)PW(X)^*`, `X in (r/12)S`, are pairwise
`rho`-separated by at least `(s/2)(r/48) = s^2/960 >= 1/(960 q)`. For `eps < 1/(2000q)`, two
microstates at distance `> 2 eps` cannot share an `eps`-ball, so

```text
N_eps(Mic(sigma~,F,delta),rho) >= |S| >= (1/2)(16/e)^(M^2),
(dm)^(-beta) log N_eps >= (m^(2-beta)/(4 d^beta)) log(16/e) - o(1) -> infinity.
```

This holds for every `(F,delta)` with `delta < 1/(2q)` and all large `j`. So the infimum over
`(F,delta)` of the `limsup` is `+infinity` for every small `eps`. QED.

**Remark (why the full matrix commutant is needed).** Restricting to diagonal `X` (a commuting
torus in the commutant) gives only `M` real parameters. That is `(1/(dm)) log N = O(1/d)`, and
the count stays finite. The explosion comes from the `M^2`-dimensional volume of the commutant
`U(m)` of `sigma (x) 1_m`. This commutant volume is the invariant K1 isolates.

### Consequences

1. **The multinomial bound fails.** The one step every sofic lower bound for Rokhlin entropy uses
   is `h_Sigma(A^G) <= H(P)` for every generating partition `P`; it gives
   `h_Sigma <= h^Rok <= log q`. The HS count violates it along the sofic approximation
   `Sigma (x) 1` of `Z`, where `h^Rok = log q` and the count is `+infinity`. So no theorem of the
   form "HS commutative microstate entropy along unitary approximations is at most Rokhlin
   entropy" holds, even for `G = Z`.
2. **Base-blind.** The value `+infinity` does not depend on `q`, so the count cannot separate
   `A^G` from `B^G` or detect a deficit.
3. **Robust across variants.** The proof uses only the following, so K1 applies to every
   microstate space defined by joint `*`-moment conditions on `(sigma, p)`:
   - moments that are invariant under conjugation by the commutant;
   - block averaging;
   - swap invariance of the uniform base.

   This covers approximate commutation, approximate projections before functional calculus, and
   longer moment windows.

## 2. K2: the commutant quotient collapses on amenable groups (import-dependent, not load-bearing)

Quotient the microstate space by conjugation with the `eta`-approximate commutant

```text
U_eta(sigma,F) = {u in U(n): ||[u,sigma(g)]||_2 < eta, g in F},
```

with `eta` fixed independently of `delta`. On an infinite amenable `G`:

- the crossed product `L^inf(A^G) (x|) G` is the hyperfinite `II_1` factor `R`;
- two microstate sequences with the same `sigma` give two trace-preserving embeddings of `R` into
  `prod^omega M_n` that agree on `L(G)`;
- by uniqueness of embeddings of `R` up to unitary conjugacy, they are conjugate by some
  `u = (u_n)`. That `u` fixes `sigma(G)` in the ultraproduct, so its lifts lie in `U_eta` along `omega`.

A contradiction argument over `(F_k,delta_k,n_k)` then shows that, for every `eps` and `eta`, the
quotient count is eventually `1`. So this species gives `0` for every base on amenable `G`, and
is base-blind at `0`.

The uniqueness theorem is standard (Connes; Jung, Math. Ann. 338 (2007)), but no verbatim
citation is imported here, so K2 stays under Attempts. It is not used by K1.

At scale `n^2` the same collapse is supplied inside the graph by
`cartan-algebras-are-strongly-one-bounded` (1-bounded entropy `<= 0`) and by
`diffuse-pin-centralizer-has-zero-quadratic-covering`.

## 3. Species census and where each dies

| species | value | dies at |
| --- | --- | --- |
| counted, commutant unrestricted (K1) | `+infinity` for all `q`, along amplifications | multinomial bound `h <= H(P)` |
| quotient by `eta`-commutant, `eta` independent of `delta` (K2) | `0` on amenable `G`, every `q` | lower bound `>= log q` (base-blind at zero) |
| diagonal / permutation (the original sofic entropy) | `log q` on sofic `G` | existence: coherent actor tables exist iff the Bernoulli action is sofic (`coherent-bernoulli-actor-tables-are-cartan-soficity`), which forces `G` sofic (Paunescu); empty on `U` and on every nonsofic group, which is exactly where deficits must live |
| quotient with tolerance tied, `eta = eta(delta) -> 0` | unknown | **the gate** below |

## 4. The gate that remains

**Gate (OPEN, not promoted to a node).** Let `Sigma` be a unitary approximation of a hyperlinear
group `G` that carries Bernoulli commutative microstates. Consider the orbital count

```text
N^orb_eps(F,delta) = N_eps(Mic(sigma,F,delta) / U_(eta(delta))(sigma,F), rho),    eta(delta) -> 0.
```

Does `sup_eps inf_(F,delta) limsup (1/n) log N^orb` obey the multinomial bound `<= H(P)` for
generating partitions, and is it `>= log q` along some `Sigma`?

K1 does not apply, because its rotations have `||[W,sigma]|| = 0` and are quotiented away. K2
does not settle it, because the ultraproduct uniqueness argument yields unitaries whose commutator
tolerance cannot be tied to `delta` uniformly. A positive answer on `U` needs, at minimum:

- **(P1)** `U` hyperlinear (`binary-leavitt-unit-group-hyperlinear`, OPEN);
- **(P2)** `L^inf(A^U) (x|) U = L(Z_q wr U)` Connes-embeddable. Hayes--Sale permanence assumes a
  sofic acting group, so it is not supplied (`hyperlinear-nonsofic-free-action`, Attempts);
- **(P3)** the tied-tolerance count obeys the multinomial bound. K1 kills every version with exact
  commutant freedom, so (P3) must use the decay of `eta(delta)` quantitatively;
- **(P4)** the lower bound `>= log q` along some `Sigma`. For amenable `G` the K2 mechanism
  suggests the orbital space is nearly a point, so (P4) would have to come from genuinely
  non-amenable tolerance effects.

Each of (P1)-(P4) can fail on its own. (P3) and (P4) pull in opposite directions: collapsing the
commutant volume enough for (P3) is what K2 shows kills (P4) in the amenable regime.

## 5. Verdict for the lane

The stability-approximation transplant of sofic entropy is not a route to INF on nonsofic groups:

- counted versions are `+infinity` by commutant volume (K1, established);
- quotiented versions collapse (K2);
- diagonal versions require soficity of the Bernoulli action.

Only the tied-tolerance orbital count survives, and it needs (P1)-(P4).
