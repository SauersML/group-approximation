# Local annihilation versus Stepanov's linear-dependence condition (b): credit decision

Lane `un-stepanov-credit` (UN swarm), 2026-09-13. Status: unreviewed. Sources read from primary PDFs fetched on MSI.

## 0. Question and verdict

`local-annihilation-makes-projective-el-simple` (Lean: `GroupApproximation.Pestov91.isSimpleGroup_elementaryGroup_quotient_center`)
proves: for a unital simple ring `R` with local annihilation and `n ≥ 3`, every normal subgroup of `EL_n(R)` is central
or everything. un-novelty (part 2, item 1) flagged Stepanov 1997 as a possible prior source. Is the criterion a special
case?

**Verdict.**
1. **Method: PRIOR.** The criterion's proof is Stepanov's Lemma 4.3 extraction, fed a noncentral element that local
   annihilation supplies (§3). Credit Stepanov for the extraction step.
2. **Hypothesis: not a weakening of Stepanov's (b).** Every simple Artinian ring satisfies (a) and (b) for `n ≥ 3`, and
   none has local annihilation (§2, `division-rings-satisfy-stepanov-b-not-local-annihilation`).
3. **Undecided:** whether local annihilation implies (b) (`local-annihilation-implies-stepanov-condition-b`, §4). Until
   it is settled, the criterion is NEW (bounded) as a sufficient condition. The rings it covers (Steinberg algebras,
   including purely infinite ones such as `L_k(1,d)`) are not known to satisfy Stepanov's (b) or Vaserstein's
   hypotheses (§5).

## 1. The sources, specialized to simple rings

Stepanov, J. Math. Sci. 95 (1999) 2146–2155 (Zap. POMI 236, 1997), pp. 2151–2152, verbatim in
`stepanov-linear-dependence-standard-normal-structure`. That node quotes Lemma 4.1 (unimodular column α with
`α_i = (cα)_j = 0` ⇒ `c` central), Lemma 4.3 (`ξc_ij = 0` ⇒ `ξ ∈ I^⊥(c)`) and Theorem 4.4 (conditions (a), (b) for
every proper ideal ⇒ standard normal structure).

For simple `R` the only proper ideal is `0`:
- (a) reads `[GL(n,R,0), E(n,R)] = E(n,R,0)`, which is trivial since both sides are `{e}`;
- (b) reads: every `a ∈ GL(n,R)` has `b ∈ E(n,R)` and `α ∈ R^n`, `α ≠ 0`, with `α_i = (a^b α)_j = 0`;
- in the proof of Theorem 4.4, `I^⊥(a) = 0` for noncentral `a`, because `I(a) = R`. So (b) is applied to `a` itself.

## 2. Separation: (b) does not imply local annihilation

Let `R = M_m(D)`, `D` a division ring, and `n ≥ 3`.
- **(b) holds, with `b = 1`.** Write `R^n` as `nm × m` matrices over `D` and restrict to `α` supported in the first
  `D`-column. The conditions `α_i = 0` and `(uα)_j = 0` are `2m` right-linear equations in `nm ≥ 3m` unknowns over
  `D`, so a nonzero solution exists.
- **Local annihilation fails.** With `F = {E_(ij)}`, `t ≠ 0` and `tE_(ij)s = 0` for all `i, j` force `s = 0`, since
  `t_(pi) s_(jq)` is the `(p,q)` entry and some `t_(pi)` is invertible. So `S_F = {0}`.

So Stepanov covers all simple Artinian rings, and local annihilation covers none. More generally, local annihilation
forces `R` not to be Artinian, because a finite spanning set over a division ring gives `S_F = 0` as above.

## 3. The criterion factors through Stepanov's Lemma 4.3

Proof of `local-annihilation-makes-projective-el-simple`, as in `SimpleModCentre.lean`:
1. `N ⊴ EL_n(R)` is noncentral with noncentral `g ∈ N`. Local annihilation, applied to the entries of `g`, gives
   `h = e_ij(s)` not commuting with `g`, and `t ≠ 0` with `ts = 0` and `t g_pk s = 0`.
2. `ρ = [g, h] ∈ N`, `ρ ≠ 1`, and `t(ρ − 1) = 0` entrywise.

From here Stepanov's Lemma 4.3 finishes directly.
- `ρ` is noncentral: a central `ρ = ζ·1` with `t(ζ − 1) = 0` forces `ζ = 1`, because `Z(R)` is a field.
- Take `F = N` (normalized by `E(n,R) = EL_n(R)`), `c = ρ` and `ξ = t`. Then `t ρ_(ij) = 0` for `i ≠ j`.
- If `N` contained no nontrivial transvection, Lemma 4.3 would put `t ∈ I^⊥(ρ) = 0`, because `I(ρ) = R` for
  noncentral `ρ` in a simple ring. That contradicts `t ≠ 0`.
- So `N` contains `t_ij(x)` with `x ≠ 0`. Its associated ideal is nonzero, hence equal to `R`, so `N ⊇ E(n,R)`.

The Lean file proves its own extraction and imports nothing from Stepanov. The mathematical content of steps 3–4 is
Stepanov's Lemma 4.3, so the credit belongs to him. What local annihilation adds is steps 1–2: a supply of noncentral
elements with a nonzero left annihilator on an off-diagonal entry, valid in every simple ring with local annihilation,
without Stepanov's (b).

## 4. Does local annihilation imply (b)? Open

Attempts, recorded on `local-annihilation-implies-stepanov-condition-b`:
- a zero-divisor entry of a conjugate gives (b), but local annihilation yields left annihilators, the wrong side;
- at `b = 1` there are counterexample rows in `L_k(1,2)` (orthogonal isometries admit no right relation), so any proof
  must use nontrivial conjugation;
- the opposite-ring form gives two-sided annihilation `s a_(pq) t = 0`, not a zero entry.

A proof would make the simplicity criterion literally a special case of Theorem 4.4. A counterexample would need a
simple ring with local annihilation where some `a ∈ GL_n(R)` keeps every nonzero `α` with `α_i = 0` off the
coordinate hyperplanes under all `E(n,R)`-conjugates. Leavitt algebras of infinite stable rank are the natural place to
look. Neither was found.

## 5. Vaserstein, LNM 854 (1981)

Verbatim in `vaserstein-local-stable-range-normal-subgroups`.
- **Theorem 4:** a local stable range `sr(S^{-1}A) ≤ n − 1` gives standard structure (2).
- **Theorem 19:** a column-reduction condition, for every `g ∈ GL_n A`, gives `H ⊃ E_n(A, J(H))`.

For simple `A` with centre a field, Theorem 4 needs `sr(A) ≤ n − 1`, and Theorem 19 needs, for each `g`, some
`Σ_(i<n) b_i(g_(i1) + a_i g_(n1)) = 1`. Local annihilation gives neither. Purely infinite simple rings such as
`L_k(1,2)` are not of stable rank 1, so Theorem 4 does not obviously apply to them. Theorem 19's hypothesis for them is
not decided here.

## 6. Credit wording for the simplicity nodes

"The extraction step (a nonzero left annihilator of an off-diagonal entry of a noncentral element of a normal subgroup
forces a transvection) is Stepanov's Lemma 4.3 (J. Math. Sci. 95 (1999), p. 2151). The criterion's new part is the
hypothesis: local annihilation supplies such elements in every simple ring with local annihilation. It is not implied
by Stepanov's Theorem 4.4 condition (b), since simple Artinian rings satisfy (b) but not local annihilation. Whether it
implies (b) is open (`local-annihilation-implies-stepanov-condition-b`)."
