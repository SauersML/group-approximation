---
rg: 2
id: finite-index-compression-collapse-needs-only-model-gap-proof
kind: route
title: Average the cocycle over the finitely many cosets of the compressed copy, then transport through the eigenprojection of one Markov element in the finite adjoint corona
target: finite-index-compression-collapse-needs-only-model-gap
requires: []
artifacts:
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
---

Notation is that of the target and of section 2 of
`notes/COMPRESSION_COLLAPSE_MF_RADICAL.md`.  Put `H = s Lambda s^-1`,
`m_0 = [Lambda : H] < infinity`, and fix left coset representatives
`lambda_1, ..., lambda_{m_0}` of `Lambda / H`.

## Step 0: which steps of the note use (T)

The note uses (T) only in Steps 3, 5 and 6, as its own final remark
says.  Steps 1, 2 and 4 use only the image hypotheses on `k`, the lifts
`U_{g,n}` and the lifting hypothesis (L):

- Step 1: exact commuting lifts `v_{lambda,n}`, rigidity, rank metric.
- Step 2: eventual invariance `d_n(g lambda, g mu) = d_n(lambda, mu)`.
- Step 4: the rescaled space `K_omega`, the representation `sigma`, and
  the cocycle `c`.

Step 3 uses (T) only to obtain a finite generating set `S`; hypothesis
(F) supplies it.  With `S` fixed, `k_n = sum_{a in S} d_n(1,a)` and the
word bound `d_n(1,lambda) <= r k_n` hold verbatim.

So, arguing by contradiction as in the note, suppose `lambda_0 in Lambda`
has `pi(lambda_0 k lambda_0^-1) != pi(k)`.  Choose `omega` as in Step 3.
Step 4 then yields:

- (a) a genuine unitary representation `sigma` of `W` on `K_omega`,
  induced by `Ad U_{g,n}`;
- (b) a genuine 1-cocycle `c : Lambda -> K_omega` for `sigma|_Lambda`;
- (c) `c != 0`, since `sum_{a in S} ||c(a)||^2 >= eta_m^2 > 0`;
- (d) `c(h) = 0` exactly for every `h in H`.  Indeed
  `v_{h,n} = v_{1,n}` for all large `n` by rigidity and hypothesis (3),
  so `c_n(h) = 0` eventually.

It remains to derive a contradiction from (a)-(d) using (I) and (MSG)
only.

## Step 5 replaced: the coset-average primitive

**Lemma 1.**  Let `rho` be a unitary representation of a group `Lambda`
on a Hilbert space `K`, let `H <= Lambda` have finite index `m_0`, and
let `c` be a cocycle, `c(xy) = c(x) + rho(x) c(y)`, with `c|_H = 0`.  Put

```text
w = - (1/m_0) sum_{i=1}^{m_0} c(lambda_i).
```

Then `c(g) = rho(g) w - w` for every `g in Lambda`, and `w` is `H`-fixed.

*Proof.*  First, `c` is constant on left cosets:
`c(lambda h) = c(lambda) + rho(lambda) c(h) = c(lambda)`.  So
`C(xH) := c(x)` is well defined on `Lambda/H`, and `w` does not depend
on the choice of representatives.  For `g in Lambda`, the cocycle
identity gives `rho(g) c(lambda_i) = c(g lambda_i) - c(g)`.  Hence

```text
rho(g) w - w
  = -(1/m_0) sum_i [ c(g lambda_i) - c(g) ] + (1/m_0) sum_i c(lambda_i)
  = c(g) - (1/m_0) sum_i C(g lambda_i H) + (1/m_0) sum_i C(lambda_i H)
  = c(g).
```

The last equality holds because `x H -> g x H` permutes `Lambda/H`.  For
`h in H`, `rho(h) w - w = c(h) = 0`.  QED.

Apply Lemma 1 to `rho = sigma|_Lambda` on `K_omega`.  This gives an
`H`-fixed `w in K_omega` with `c(g) = sigma(g) w - w`.  No property of
`Lambda` beyond (I) was used; in particular neither FH nor
Delorme--Guichardet nor the Gaussian kernel appears.

## Step 6 replaced: transport through one eigenprojection

**The action of `B` on `K_omega`.**  A vector of `K_omega` is a sequence
`(x_n)`, `x_n in M_{d_n}`, with `sup_n Tr|x_n|^2 / k_n < infinity`,
modulo `omega`-null sequences.  An operator on `(M_{d_n}, ||.||_2)` has
the same norm for the rescaled inner product `Tr(y^* x)/k_n`.  So a
bounded sequence `(T_n)` acts on `K_omega` coordinatewise, and a sequence
with `||T_n|| -> 0` acts as `0`.  This defines a unital
`*`-homomorphism `pi_K : B -> B(K_omega)` with
`pi_K(sigma~(g)) = sigma(g)`.

**Lemma 2 (the adjoint corona is finite).**  Let `P <= Q` be projections
in `B` with `Q = V P V^*` for a unitary `V in B`.  Then `P = Q`.

*Proof.*  Put `E = Q - P`, a projection with `PE = 0`.

- Lift `P` to projections `p_n`.  Take any self-adjoint lift; its
  spectrum eventually lies near `{0,1}`; apply `chi_{(1/2,inf)}`.
- Let `e'_n` be a self-adjoint lift of `E`, and put
  `b_n = (1-p_n) e'_n (1-p_n)`, a lift of `(1-P)E(1-P) = E`.  Its
  spectrum is eventually within `1/4` of `{0,1}`.
- `f_n = chi_{(1/2,inf)}(b_n)` is a projection with `f_n p_n = 0`,
  because `b_n p_n = p_n b_n = 0`.  Also `||f_n - b_n|| -> 0`, so
  `[(f_n)] = E`.
- Lift `V` to unitaries `V_n`, using polar parts of an eventually
  invertible lift.

Then `||V_n p_n V_n^* - (p_n + f_n)|| -> 0`.  Projections at distance `< 1`
have equal rank, so `rank p_n = rank p_n + rank f_n` for large `n`.
Hence `f_n = 0` eventually and `E = 0`.  QED.

**Lemma 3 (the substitute projection).**  Put `y = sigma~(h_S)` and
`P = chi_{1}(y)`, which lies in `B` by (MSG).  (If `1 notin sp(y)`, then
`P = 0`.)  Then:

- (i) `sigma~(lambda) P = P` for `lambda in Lambda`;
- (ii) `pi_K(P)` is the orthogonal projection onto
  `Fix sigma(Lambda) subset K_omega`;
- (iii) `Q := sigma~(s) P sigma~(s)^*` satisfies `P <= Q`, hence `Q = P`.

*Proof.*

(i) `yP = P` gives `P(1-y)P = 0`.  For a unitary `u` we have
`1 - Re u = (1/2)(1-u)^*(1-u)`, so

```text
0 = |S|^-1 sum_{a in S} (1/2) ((1-sigma~(a))P)^* ((1-sigma~(a))P).
```

The sum is of positive terms, so `sigma~(a) P = P` for every `a in S`.
Since `S` generates `Lambda`, (i) follows.

(ii) By (i) the range of `pi_K(P)` is fixed.  Conversely, let
`pi_K(y) xi = xi`.  Then `p(pi_K(y)) xi = p(1) xi` for every polynomial
`p`, and hence for every continuous function on `sp(y)`, which contains
`sp(pi_K(y))`.  `chi_{1}` is such a function by (MSG).  So
`pi_K(P) xi = xi`.  Every fixed vector satisfies `pi_K(y) xi = xi`.

(iii) `sigma~` is a genuine homomorphism, so
`y' := sigma~(s) y sigma~(s)^* = |S|^-1 sum_{a in S} sigma~(s a s^-1)`.
Each `s a s^-1` lies in `H`, which is contained in `Lambda`, so
`y' P = P` by (i).  Also `sp(y') = sp(y)`.  So the polynomial argument
of (ii) gives `Q P = chi_{1}(y') P = P`, that is, `P <= Q`.  Lemma 2,
with `V = sigma~(s)`, gives `Q = P`.  QED.

**Conclusion.**  Let `w` be the `H`-fixed primitive of Lemma 1 and put
`u = sigma(s)^-1 w`.

For `lambda in Lambda`, `s lambda s^-1 in H`, so

```text
sigma(lambda) u = sigma(s^-1) sigma(s lambda s^-1) w = sigma(s^-1) w = u.
```

So `u in Fix sigma(Lambda)`, and `pi_K(P) u = u` by Lemma 3(ii).  Then

```text
w = sigma(s) u = pi_K(sigma~(s) P) u = pi_K(Q sigma~(s)) u
  = pi_K(P) sigma(s) u = pi_K(P) w.
```

So `w in Fix sigma(Lambda)` and `c(g) = sigma(g) w - w = 0` for every
`g in Lambda`, contradicting (c).  Hence
`pi(lambda k lambda^-1) = pi(k)` for all `lambda in Lambda`.  QED.

## Sanity checks

- *Recovery of Theorem 1 at finite index.*  If `Lambda` has (T) with
  Kazhdan pair `(S, kappa)`, then (F) holds.  Also
  `sp(y) subset [-1, 1 - kappa^2/(2|S|)] union {1}` in every C-star
  target (`kesten-spectral-gap-replaces-kazhdan-projection-per-model`,
  item 2), so (MSG) holds.
- *Amenable calibration.*  For `Lambda = Z`, `s` the doubling in
  `BS(1,2)`, index 2, the note's cyclic-base calibration (section 7:
  `BS(1,2)` base, amenable witness group, MF by TWW) shows that the
  collapse conclusion fails.  So (MSG) must fail on `Z` in some corona model of it.
  This is consistent with
  `amenable-subgroup-fixed-projection-is-never-in-adjoint-corona`, which
  excludes `P_L` from `B` for amenable `L` with an infinite `L`-class in
  `delta_e`-profile models.
- *Where the theorem is used.*  The finite index is used only in
  Lemma 1.  Lemmas 2 and 3 hold for every compression.  So at infinite
  index the only missing input is an `H`-fixed primitive of `c`.  (MSG)
  does not supply one: a spectral gap does not kill `H^1`, as the
  regular representation of `F_2` shows.
