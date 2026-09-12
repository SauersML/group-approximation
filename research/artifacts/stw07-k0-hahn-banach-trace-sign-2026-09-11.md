# STW Problem VII: the K_0-Hahn--Banach property is a trace-sign problem (2026-09-11)

Lane `stw-bk`.  Sources read for this artifact: Brown--Dadarlat, *Extensions of
quasidiagonal C*-algebras and K-theory*, arXiv:math/0008182 (Theorem 3.4,
Definition 4.8, Theorem 4.11); Moutzouris, *Extensions of quasidiagonal
C*-algebras and controlling the K_0-map of embeddings*, arXiv:2112.03224v3
(Definitions 2.2--2.4, Remark 2.5, Theorem 1.3); Gabe, arXiv:1804.08095
(Corollaries B--D); STW arXiv:2506.10902v2, Problem VII.

Conventions.  `A` is separable and unital unless said otherwise.  A *model*
of `A` is a sequence of c.c.p. maps `phi_n: A -> M_(k_n)` with
`||phi_n(ab)-phi_n(a)phi_n(b)|| -> 0`; it is *faithful* when also
`||phi_n(a)|| -> ||a||`.  For projections `p,q in M_N(A)` and large `n`,
`phi_n(p)` is within `1/4` of a unique spectral projection `P_n`; put
`(phi_n)_*([p]-[q]) = rank P_n - rank Q_n`.  On any finitely generated part of
`K_0(A)` this is eventually a well-defined homomorphism, because the finitely
many Murray--von Neumann relations involved are implemented by partial
isometries, which models carry to approximate partial isometries with equal
source and range ranks.  An element `x in K_0(A)` is *singular* when
`Zx cap K_0^+(A) = {0}` (Moutzouris, Def. 2.4).  The K_0-Hahn--Banach property
(Brown--Dadarlat Def. 4.8) asks for faithful models with `(phi_n)_*(x)=0` for
large `n`, for every singular `x`.

For a tracial state `tau` write `x^(tau) = (Tr tensor tau)(p-q)`.

## 0. What Brown--Dadarlat and Moutzouris give

- BD Thm 3.4: `0 -> I -> E -> B -> 0`, `E` separable, `I` QD, `B` nuclear QD
  UCT, and `d: K_1(B) -> K_0(I)` zero, then `E` is QD.
- BD Thm 4.11: every separable nuclear QD algebra has the QD extension property
  iff every one has the K_0-embedding property iff every one has the
  K_0-Hahn--Banach property iff every singular `x` is the index of the
  generator of `K_1(C(T))` in some QD extension of `C(T)` by `K tensor A`.
- Moutzouris Remark 2.5: if the ideal has the K_0-embedding property and the
  quotient is separable nuclear QD UCT, then the extension is QD iff stably
  finite.  Thm 1.3: this holds when `A tensor Q` is locally approximated by
  finite direct sums of separable ASH algebras and `D x| Z` (minimal, invariant
  trace, `D` UCT).

So the Blackadar--Kirchberg problem restricted to extensions with a UCT
quotient is equivalent to the K_0-Hahn--Banach property for all separable
nuclear QD algebras.  Everything below is about that property.

## 1. Model values are trace values

**Lemma 1.**  Let `phi_n` be a model of `A` with `phi_n(1)` not asymptotically
zero.  Then after compressing to the spectral projection of `phi_n(1)` the maps
are approximately unital, the states `omega_n = tr o phi_n` are asymptotically
tracial, and every weak* cluster point of `(omega_n)` is a quasidiagonal
tracial state.  Moreover

```text
(phi_n)_*(x) = k_n ( omega_n(x^) + o(1) ).                         (V1)
```

*Proof.*  Asymptotic multiplicativity gives `phi_n(1)^2 ~ phi_n(1)`, so its
spectral projection `e_n` satisfies `||phi_n(1)-e_n|| -> 0` and
`phi_n(a) ~ e_n phi_n(a) e_n`.  Compressing changes ranks of the `P_n` by zero
for large `n`.  `|omega_n(ab-ba)|` is bounded by the two multiplicativity
defects, so cluster points are tracial; a cluster point along a subsequence is
quasidiagonal by Brown's definition.  For `(V1)`, `|Tr(phi_n(p)) - rank P_n|`
is at most `N k_n ||phi_n(p)-P_n||`, and `||phi_n(p)-P_n|| -> 0`. QED

## 2. Theorem A: a class positive on QD traces obstructs quasidiagonal extensions

**Theorem A.**  Let `A` be separable, unital, quasidiagonal, and let
`x in K_0(A)` be singular with `x^(tau) > 0` for every quasidiagonal tracial
state `tau`.  Then:

1. no model of `A` (faithful or not, not asymptotically zero) kills `x`: its
   value is eventually strictly positive;
2. any extension `0 -> K tensor A -> E -> C(T) -> 0` whose index map sends the
   generator `[z]` of `K_1(C(T))` to `x` (such extensions exist: `C(T)`
   satisfies the UCT, so Ext maps onto `Hom(K_1(C(T)),K_0(A))`) is separable,
   unital, stably finite, and **not quasidiagonal**;
3. if `A` is nuclear, `E` is nuclear; hence `E` answers STW Problem VII in the
   negative, and it is also a counterexample to Moutzouris' Conjecture 1.2
   with UCT quotient `C(T)`.

*Proof.*  (1) If along a subsequence `(phi_n)_*(x) <= 0`, then by `(V1)`
`omega_n(x^) <= o(1)` there, and a further cluster point `tau` is a QD trace
with `x^(tau) <= 0`, a contradiction.  No closedness of the QD trace set is
used.

(2) Stable finiteness.  Let `v in M_m(E)` with `v*v=1`.  Its image in
`M_m(C(T))` is an isometry, hence unitary, so `p = 1-vv* in M_m(K tensor A)`
and `-[p]` is the index of that unitary, so `-[p] in Zx`.  If `[p]!=0` then
`[p]` is a nonzero positive element of `Zx`, contradicting singularity.  So
`[p]=0`, and stable finiteness of `K tensor A` (it is QD) forces `p=0`.

Non-quasidiagonality.  Let `psi_n` be a faithful unital model of `E`.  By
exactness of the six-term sequence, `iota_*(x) = iota_*(d[z]) = 0` in
`K_0(E)`.  So there are a projection `r` and a partial isometry `w` over `E`
with `w*w = p (+) r` and `ww* = q (+) r`, where `x = [p]-[q]` and
`p,q in M_N(A tensor e_11)`.  For large `n`, `X = psi_n(w)` satisfies
`X*X ~ psi_n(p (+) r)` and `XX* ~ psi_n(q (+) r)`.  Since `X*X` and `XX*` have
the same nonzero spectrum with multiplicity, the spectral projections near
`psi_n(p (+) r)` and `psi_n(q (+) r)` have equal rank, so `(psi_n)_*(x) = 0`.

(Existence of a unital extension with index `x`: `K_1(Q(K tensor A)) ~= K_0(A)`
through the index map, since `K_*(M(K tensor A)) = 0`.  Take a unitary
`u in Q(K tensor A)` of index `x`, after absorbing matrices into `K`, and the
unital Busby map `z -> u`.  The resulting `E` is separable.)  Restricting `psi_n` to `A tensor e_11 = A` gives
a model of `A` that is not asymptotically zero, since `psi_n` is faithful,
with value `0` on `x`.  This contradicts (1).

(3) Nuclearity passes to extensions of nuclear algebras. QED

## 3. Theorem B: sign changes on QD traces are killed

**Theorem B.**  Let `A` be separable unital QD and `x` singular.  If there are
QD tracial states `tau_+`, `tau_-` with `x^(tau_+) > 0 > x^(tau_-)`, then some
faithful model of `A` kills `x`.

*Proof.*  Take a faithful model `psi` with values `a_n`, and models
`sigma^+`, `sigma^-` whose trace states converge to `tau_+`, `tau_-`.  By
`(V1)` their values `b_n`, `c_n` are eventually `>0` and `<0`.  If `a_n>0` use
`|c_n|` copies of `psi_n` and `a_n` copies of `sigma^-_n`; if `a_n<0` use
`b_n` copies of `psi_n` and `|a_n|` copies of `sigma^+_n`; if `a_n=0` use
`psi_n`.  Direct sums with `n`-dependent multiplicities keep the
multiplicativity defect and norm lower bound, since norms of direct sums are
maxima.  So the result is a faithful model with value `0`. QED

## 4. Theorem C: singular classes change sign or sit on the boundary

**Lemma 2 (ordered groups).**  Let `(G,G^+,u)` be a partially ordered abelian
group with order unit and `x in G`.  If `mx >= u` holds for no `m >= 1`, some
state `s` has `s(x) <= 0`.

*Proof.*  By the Goodearl--Handelman state extension theorem, the state
`s_0(ku)=k` on `Zu` extends to states of `G` whose values at `x` fill
`[f_*, f^*]` with `f_*(x) = sup{k/m : m>=1, ku <= mx}`.  If `ku <= mx` with
`k>=1` then `u <= ku <= mx`, which is excluded, so every admissible `k` is
`<= 0` and `f_*(x) <= 0`.  An extension attaining `f_*(x)` works. QED

**Theorem C.**  Let `A` be separable unital exact and stably finite, and `x`
singular.  Then `x^` is not strictly positive on `T(A)` and not strictly
negative.  Hence `x^` either takes both strict signs, or is `>= 0` on `T(A)`
with a nonempty zero face, or is `<= 0` with a nonempty zero face.

*Proof.*  Stable finiteness makes `([1], K_0^+)` an order unit of an ordered
group.  Every state on `K_0(A)` is induced by a quasitrace
(Blackadar--Rordam, J. Algebra 152 (1992)), which is a trace by exactness
(Haagerup).  If `x^ > 0` on `T(A)`, every state is `>0` at `x`, so Lemma 2 gives
`mx >= [1] >= 0` for some `m`, contradicting singularity.  Apply the same to
`-x`. QED

**Corollary D.**  If `A` is separable unital nuclear QD and every tracial state
is QD, then every singular `x` with a strict sign change is killed
(Theorems B and C), and the K_0-Hahn--Banach property for `A` reduces exactly
to **boundary** singular classes: `x^ >= 0` on `T(A)` with a nonempty zero face.

## 5. What a Theorem A counterexample would cost

**Theorem E.**  If `A` and `x` are as in Theorem A with `A` nuclear, then
Theorem C yields a tracial state `sigma` with `x^(sigma) <= 0`.  So `sigma` is
not quasidiagonal, and the quotient `A/J_sigma` by its trace kernel is a
separable nuclear algebra with a faithful amenable, non-quasidiagonal trace.
By Schafhauser's trace-extending AF-embedding theorem (the UCT case of STW
Theorem 11), `A/J_sigma` does not satisfy the UCT.  In particular the exact
residual of X(1) fails, and the UCT problem (STW II) has a negative answer on
a quotient of `A`.

*Proof.*  A QD trace on the quotient pulls back to a QD trace on `A`, since
composing models with the quotient map keeps multiplicativity, so the induced
trace of `sigma` is not QD.  An AF embedding extending a faithful trace makes
that trace QD. QED

So the only Problem VII counterexample this mechanism can manufacture sits
behind two open negative answers (exact X(1) and a non-UCT nuclear quotient).
Conversely, under "all traces QD" (for instance all quotients UCT), the entire
K_0-Hahn--Banach question is the boundary case of Corollary D.

## 6. No ordered-group obstruction on finite data (why the boundary case is analytic)

**Lemma 3.**  Let `A` be stably finite and `x` singular.  For finitely many
nonzero projection classes `[p_i]`, finitely many positive classes `y_j`, and a
finitely generated subgroup containing them and `x`, there is a homomorphism
`r` to `Z` with `r(x)=0` (respectively `r(x)=-1`), `r(y_j)>=0`, `r([p_i])>=1`.

*Proof.*  Rational feasibility suffices (scale).  By Motzkin's alternative,
infeasibility gives nonnegative rationals, not all `mu_i` zero, with
`sum mu_i [p_i] + sum lambda_j y_j in Q x`; clearing denominators puts a
nonzero positive class in `Zx`.  Nonzero because stable finiteness makes
nonzero projections have nonzero classes that cannot cancel.  That contradicts
singularity.  For `r(x)=-1`, infeasibility gives `lambda_0 x` equal to a
positive class with `lambda_0>0`, or a vanishing nonzero positive combination;
both are excluded the same way. QED

So on every finite window the rank data needed to kill, or even to negate, a
singular class exist.  What can fail is only their realisation by an actual
model, and for boundary classes `(V1)` allows values of size `o(k_n)` of either
sign.  That realisation problem is the open hinge.

## 7. Theorem G: quotient models supply the missing signs

**Theorem B'.**  The balancing in Theorem B only needs models of either sign;
they need not track traces or be faithful.  So `x` is killed as soon as
some models, faithful or not, have eventually positive values and others
eventually negative ones.  A faithful model contributes any sign and is
balanced against the opposite side.

**Theorem G.**  Let `A` be separable, unital, nuclear and quasidiagonal, and
`tau` a tracial state with `tau^(x)=0`.  If `A/J_tau` satisfies the UCT and
the image of `x` in `K_0(A/J_tau)` is non-torsion, then `x` is killed by a
faithful model.

*Proof.*  Moutzouris Proposition 4.3 applies to the faithful trace on the
quotient.  It gives faithful unital maps `A/J_tau -> B_1, B_2` into AF
algebras with values `>0` and `<0` on the image of `x`.  A nonzero positive
element of `K_0` of an AF algebra is a nonzero positive vector at some finite
stage, so faithful stage representations give eventually positive ranks, and
negative values likewise.  Compose with the quotient map and apply
Theorem B'. QED

## 8. The sharpened residual

Assume every trace-kernel quotient of `A` satisfies the UCT (for example `A`
of type I, or all quotients in the bootstrap class) and all traces are QD.
Combining Theorems B, C and G, a singular `x` survives only if, up to
replacing `x` by `-x`:

1. `x^ >= 0` on `T(A)` with nonempty zero face `F`;
2. for every `tau in F`, the image of `x` in `K_0(A/J_tau)` is torsion.

Put `J_F = J_(tau_F)`, where `tau_F` is a countable convex combination of a
dense sequence in `F`, so that `J_F` is the intersection of the kernels over
`F`.  Replacing `x` by a multiple, `x` comes from `K_0(J_F)`, since the
six-term sequence is exact and torsion is killed by a multiple.  Every trace
of `A` nonzero on `J_F` lies outside `F`, so it is strictly positive on `x`.
When `J_F` has a full projection `e`, Lemma 2 applied to `eJ_Fe` (its states
are Blackadar--Rordam--Haagerup traces of the corner) shows some corner trace
is `<= 0` on the class.  Otherwise the class `y` with `mx = iota_*(y)` would be
positive in `K_0(J_F)`, and then `x` would be positive.  Without a full
projection this last step is only a heuristic.

The residual is therefore: **a class supported on an ideal, positive on
every bounded trace of `A` that sees the ideal, and nonpositive only on
unbounded or corner traces of the ideal.**  Models of corners of `J_F` with
negative values exist in the UCT setting, but models of an ideal do not
extend to asymptotically multiplicative models of `A`.  Extending ideal
models, as in Moutzouris Propositions 3.1--3.2 through absorbing extensions
and Ext-triviality, is the precise open step.
