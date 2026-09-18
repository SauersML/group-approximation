---
rg: 2
id: type-f-group-receives-re-languages-by-pattern-reductions-proof
kind: route
title: "Proof: compress the Boone configuration words by a stable letter that fixes t and x and multiplies y, and read the input's binary digits letter by letter"
target: type-f-group-receives-re-languages-by-pattern-reductions
requires:
  - boone-final-group-is-of-type-f
  - boone-final-group-finitely-presented
  - boone-commutator-criterion-for-halting
  - boone-hnn-tower-embeds-base-group
  - boone-base-group-two-generator-one-relator
artifacts:
  - experiments/boone-pattern-reductions-2026-09-17/check_pattern_words.py
  - experiments/boone-pattern-reductions-2026-09-17/results.txt
---

Verification tier: proposed-established. Steps 0 and 1 use theorems that are
already machine-checked in `GroupApproximation/Computability`. Step 0 also
reuses a machine-checked proof body for a different code, which is not a new
Lean theorem. Steps 2 to 7 are paper proofs. The Horner identity of Step 3 and the
free-word identity of Step 4 are also checked by the experiment.

## Step 0. The compile chain for an arbitrary `ToPartrec` code

**Lemma 0.** For every `c : ToPartrec.Code` there are a modular machine `M_c`,
a constant `a_c`, a modulus `m_c = M_c.size >= 2` and naturals `c_cons`,
`c_0`, `c_1` such that, with

    f_c(n) = (a_c, encList m_c (front(n)))
    front(n) = c_cons :: (trNat n).reverse.map (bit0 -> c_0, bit1 -> c_1),

for every `n`, `M_c.Halts (f_c(n)) <-> (ToPartrec.Code.eval c [n]).Dom`.

*Proof.* The proof of `exists_modularMachine_universal_control`
(`ModularMachineConfigHalting.lean`) uses a special property of its code `c`
only once, in the final `.trans (hc m)`. Everything else holds for every code:
`tr_supports c Cont'.halt`, and `tm0_eval_dom_iff c [m]`
(`UniversalMachineInit.lean`, stated for arbitrary `c`).

Delete the final `.trans (hc m)`. What is left proves
`(D.toQuad M₁).toModular.Halts (f m) <-> (ToPartrec.Code.eval c [m]).Dom`,
with `f m = (D.toQuad M₁).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m])))`.

- `encCfg_initQCfg` rewrites `f m` to `(tagA (stIdx default false true), encList (D.toQuad M₁).m (l.map encodeSym))`.
- `map_enc_trInit` rewrites the digit list to `enc(true, cons) :: (trNat m).reverse.map (fun a => enc(false, a))`.
- `trNat m` contains only `Γ'.bit0` and `Γ'.bit1` (`map_trNat_eq_binDigits`), so the digits are `c_cons`, `c_0` and `c_1`. These are the `encodeSym` values of three fixed symbols, hence fixed naturals.
- `m_c >= 2` is `ModularMachine.one_lt_size`. ∎

**Provenance correction.** The node `some-type-f-group-has-re-complete-word-problem`
calls the computability of the index map "by inspection". It is not: it is
`computable_index_map D M₁`, used inside `exists_modularMachine_universal_control`,
whose conjunct is `Computable f`. The words are also machine-checked:
`exists_boone_words` gives a computable `w` with
`WordProblem (finalGroupCode mm hM) (w p) <-> mm.Halts p`.

m-completeness of `WP(G_M)` then needs only the following composition. Let
`L ⊆ ℕ` be r.e.

- Choose a `Nat.Partrec.Code` `c_L` with `(eval c_L x).Dom <-> (Nat.unpair x).1 ∈ L`, using `Code.exists_code`.
- Put `g(p) = encode (Code.curry c_L p)`. This is computable by `Code.primrec₂_curry`.
- `eval (curry c_L p) 0 = eval c_L (Nat.pair p 0)` (`Code.eval_curry`).
- So `p ∈ L <-> mm.Halts (f (g p)) <-> WordProblem (w (f (g p)))`, with `mm, f` from `exists_modularMachine_universal_control 0`.

The r.e. side is `rePred_wordProblemPred` composed with the fixed code. The
many-one reduction `w ∘ f ∘ g` is total computable. Its words contain
`y^b` with `b >= m^(number of binary digits of g p)`, so their length is
exponential. The rest of this route removes that blow-up.

## Step 1. The universal code and the input encoding

Decode `n` as follows: `e(n)` is the number of initial `1`s in the
least-significant-first binary expansion of `n`, and `T(n) = n >> (e(n) + 1)`.
Both are primitive recursive. Let

    Phi(n) = Nat.Partrec.Code.eval (ofNat Code e(n)) T(n).

`Phi` is partial recursive (`Code.eval_part` composed with primitive recursive
maps). `ToPartrec.Code.exists_code`, used exactly as in
`exists_toPartrec_universal_code`, gives `c_U` with
`(eval c_U [n]).Dom <-> (Phi n).Dom`. Put `M = M_{c_U}`, `m = m_{c_U}` and
`a_0 = a_{c_U}`.

Let `A` be a finite alphabet. Fix
`k = max(1, ceil(log2 |A|))` and an injection `b : A -> {0, ..., 2^k - 1}`.
Let `beta(a)` be the `k` binary digits of `b(a)`, least significant first. For
`v = v_0 ... v_{l-1}` put

    T(v) = 2^{k l} + sum_i b(v_i) 2^{k i}.

`T` is injective: the top bit gives `l`, then the blocks give the letters. Its
image is decidable and `T` is computable, so `T(L)` is r.e. for r.e.
`L ⊆ A*`. Choose `e_L` with `dom eval(ofNat e_L) = T(L)`, and put

    n(v) = (2^{e_L} - 1) + 2^{e_L + 1} T(v).

Its least-significant-first bits are `1^{e_L} 0 beta(v_0) ... beta(v_{l-1}) 1`.
So `e(n(v)) = e_L` and `T(n(v)) = T(v)`, and

    v ∈ L  <->  Phi(n(v))↓  <->  M.Halts (a_0, B(v)),   B(v) = encList m (front(n(v))).

By `trNat_eq_cons`, iterated (`n(v) > 0`), `trNat n(v)` is this bit list with
`bit1`/`bit0`. Reversing it and prepending `c_cons` gives the digit list, least
significant first:

    d_0 ... d_N = c_cons, c_1, rev beta(v_{l-1}), ..., rev beta(v_0), c_0, c_1^{e_L}

(each bit replaced by its code), with `N = e_L + 2 + k l`.

## Step 2. The host `H_M` is of type F and contains `G_M`

Let `B = <t, x, y> ≤ G_M`. By `boone-hnn-tower-embeds-base-group`, the base
group `<t,x,y | [x,y]> = Z * Z^2` embeds in the tower `G'_M`. The tower embeds
in `G_M`, which is an HNN extension of it. So `B ≅ Z * Z^2`. The endomorphism

    sigma : B -> B,   t -> t,  x -> x,  y -> y^m    (m >= 2)

is injective. It is the free product of `id_Z` with the injective map
`(x,y) -> (x, y^m)` of `Z^2`, and a free product of injective maps is injective
(normal forms). So `B -> G_M` and `sigma` followed by `B -> G_M` are both
injective, and

    H_M = < G_M, s | s^-1 t s = t,  s^-1 x s = x,  s^-1 y s = y^m >

is an HNN extension of `G_M` with associated subgroups `B` and `sigma(B)`.
`G_M` embeds in it by Britton's lemma.

**Classifying space.** `boone-final-group-is-of-type-f` gives a finite
aspherical 3-complex `X` with `π1 X = G_M`.

- Let `E = S^1 v T^2`, a `K(B,1)`.
- Let `f_0 : E -> X` realize the inclusion `B -> G_M`.
- Let `f_1 = f_0 ∘ (id v p)`, where `p : T^2 -> T^2` is the covering map of degree `(1, m)`. It realizes `sigma` followed by the inclusion.
- Glue `E × [0,1]` to `X` by `f_0` at one end and `f_1` at the other.

This is a graph of spaces with vertex space `X` and edge space `E`. Both edge
maps are π1-injective, so the total space is aspherical (Scott--Wall,
Proposition 3.6, the tool of `boone-final-group-is-of-type-f-proof`). Its
fundamental group is `H_M`. It is a finite complex of dimension 3, so `H_M` is
of type `F`.

**Presentation and r.e.** A finite presentation of `G_M`
(`boone-final-group-finitely-presented`), plus the letter `s` and three
relators, presents `H_M`. So `H_M` is finitely presented and `WP(H_M)` is r.e.
(`rePred_wordProblemPred` for that presentation code).

## Step 3. Horner compression, most significant digit first

**Lemma H.** In any group where `s^-1 y s = y^m`, for all naturals
`d_0, ..., d_N`,

    y^{sum_i d_i m^i}  =  s^-(N+1) · (s y^{d_N}) (s y^{d_{N-1}}) ... (s y^{d_0}).

*Proof.* By induction on `N`. For `N = 0` the right side is `s^-1 s y^{d_0}`.
For the step, the right side is `s^-1 · [s^-N (s y^{d_N}) ... (s y^{d_1})] · s y^{d_0}`.
By induction the bracket is `y^{B'}` with `B' = sum_{i >= 1} d_i m^{i-1}`, and
`s^-1 y^{B'} s = y^{m B'}`. ∎

`check_pattern_words.py` also checks the least-significant-first variant
`y^{d_0} s^-1 y^{d_1} ... s^-1 y^{d_N} s^N` and the resulting two-homomorphism
pattern. Neither is needed below.

## Step 4. The one-homomorphism pattern

By Step 1, the digits `d_N, ..., d_0` of `B(v)`, most significant first, are
the codes of the least-significant-first bits of `n(v)`, followed by `c_cons`:

    d_N ... d_0 = c_1^{e_L}, c_0, beta(v_0), ..., beta(v_{l-1}), c_1, c_cons

(each bit replaced by its code). Let `Z(v) = (s y^{d_N}) ... (s y^{d_0})`. As
free words, letter for letter,

    Z(v) = C_1 · phi(v) · C_2,
    C_1 = (s y^{c_1})^{e_L} s y^{c_0},   C_2 = s y^{c_1} s y^{c_cons},
    phi(a) = product over the bits b of beta(a), least significant first, of s y^{c_b},

where `phi : A* -> F(gens H_M)` is ONE free-monoid homomorphism with no
inverses. By Lemma H, `u = x^{a_0} y^{B(v)} = x^{a_0} s^-(N+1) Z(v)` in `H_M`.
Since `s` commutes with `t` and `x` in `H_M`,

    t(a_0, B(v)) = u^-1 t u = Z(v)^-1 s^{N+1} (x^-{a_0} t x^{a_0}) s^-(N+1) Z(v) = Z(v)^-1 T_0 Z(v),
    T_0 = x^-{a_0} t x^{a_0}.

Put `Z_0(X) = C_1 X C_2` and

    omega_L(X) = k^-1 Z_0^-1 T_0 Z_0 k Z_0^-1 T_0^-1 Z_0.

Then `W(v) := omega_L(phi(v)) = k^-1 t(a_0,B(v)) k t(a_0,B(v))^-1` in `H_M`,
which is the element of `rawComm (a_0, B(v))`. The variable `X` occurs four
times in `omega_L`: twice as `X`, twice as `X^-1`. The length is
`|omega_L| + 4 |phi(v)|` with `|phi(a)| <= k (1 + max(c_0, c_1))`, so it is
linear in `l`, and `W(v)` is written in linear time: one forward and one
backward pass for `X^-1`.

`check_pattern_words.py` verifies, on 3000 random instances (`results.txt`):

- Lemma H in the faithful representation `y -> [[1,1],[0,1]]`, `s -> [[1/m,0],[0,1]]` of `BS(1,m)`;
- the letter-for-letter identity `Z(v) = C_1 phi(v) C_2`;
- the digit layout of Step 1, through Mathlib's least-significant-first `trNat` recurrence;
- `N = e_L + 2 + k l`.

## Step 5. Correctness

`rawComm (a_0,B) = 1` in `G_M` iff `M.Halts (a_0,B)`
(`boone-commutator-criterion-for-halting`; in Lean `commElt_eq_one_iff_halts`
through `exists_boone_words`). `G_M` embeds in `H_M` (Step 2), so the same
holds in `H_M`. With Step 1:

    v ∈ L  <->  M.Halts (a_0, B(v))  <->  W(v) = 1 in G_M  <->  omega_L(phi(v)) = 1 in H_M.

Only `omega_L` depends on `L`, through `e_L`. `phi` depends only on `A`, `b`
and `M`.

For a finitely generated recursively presented group `G` with generators `S`,
`WP(G) ⊆ (S ∪ S^-1)*` is r.e., so it is an instance with `A = S ∪ S^-1`. The
letters `a` and `a^-1` get unrelated codes, so `phi(a^-1)` is not
`phi(a)^-1`. ∎

## Step 6. Lemma E: one occurrence is embedding

**Lemma E.** Let `G = <S | R>` and `H = <T | R'>`. Let
`phi : (S ∪ S^-1)* -> F(T)` be any monoid homomorphism, let `P` and `Q` be
words and let `eps = ±1`. Suppose that for every `v`,
`v = 1` in `G` iff `P phi(v)^eps Q = 1` in `H`. Then `a -> phi(a)^eps` for
`a ∈ S` extends to an injective homomorphism `G -> H`. Conversely every
injective homomorphism gives such a reduction with `P = Q = 1`, `eps = 1`.

*Proof.* If `eps = -1`, rewrite `P phi(v)^-1 Q = 1` as `Q^-1 phi(v) P^-1 = 1`
and use `eps = 1`. Now let `eps = 1`.

- The empty word is `1` in `G`, so `PQ = 1` in `H`. Hence `v = 1` in `G` iff `phi(v) = 1` in `H`.
- For `a ∈ S`, `a a^-1 = 1` in `G`, so `phi(a) phi(a^-1) = 1` in `H`, i.e. `phi(a^-1) = phi(a)^-1` in `H`.
- So `j : F(S) -> H`, `j(a) = phi(a)`, satisfies `j(v) = phi(v)` in `H` for every word `v`.
- Relators of `G` are `1` in `G`, so they map to `1`, and `j` factors through `G`.
- If `j(v) = 1` then `phi(v) = 1`, so `v = 1` in `G`, and the factored map is injective. ∎

This holds for arbitrary `phi`: the inverse-respecting property is forced,
not assumed.

## Step 7. The obstruction

A **`r`-occurrence pattern reduction** is `v -> omega(phi(v))`, where `phi` is a
free-monoid homomorphism and `omega(X)` is a fixed word in the generators and
`X^{±1}` with exactly `r` letters `X^{±1}`. Inserting `X X^-1` changes no
value, so a relation `WP(G) <= WP(H)` witnessed at `r` is also witnessed at
`r + 2`.

- **r = 4, and every even r >= 4: dead.**
  - By Step 5, for every finitely generated recursively presented `G`, `WP(G)` reduces to `WP(H_M)` by a 4-occurrence pattern, and `H_M` is of type `F`. By padding it also reduces by an `r`-occurrence pattern for every even `r >= 4`.
  - A non-recursively-presented `G` has a non-r.e. `WP(G)`. It reduces to no r.e. set, and it embeds in no finitely presented group.
  - Let `R` be any reducibility containing the 4-occurrence patterns: linear-time, polynomial-time and log-space many-one reductions are examples. The inference "`WP(G)` is `R`-reducible to the word problem of no type `F_{n+1}` group, so `G` has no type `F_{n+1}` host" never excludes a group that r.e.-ness does not already exclude. This holds for every `n` at once.
- **r = 1: circular.** By Lemma E, "`WP(G)` reduces to `WP(H)` by a 1-occurrence pattern for some `H` of type `F_{n+1}`" is exactly "`G` embeds in a group of type `F_{n+1}`", which is Problem 1.1.
- **r = 2 and 3: open.**
  - For `omega = P X Q X^-1 R`, the empty word gives `R = (PQ)^-1`, so `omega(phi(v)) = 1` iff `phi(v)` commutes with `Q`. This is a letter-local reduction of `WP(G)` to membership in the centralizer `C_H(Q)`.
  - No embedding follows formally: the monoid `phi(A*)` acting on the coset space `H / C_H(Q)` need not give a subgroup of `H`.
  - `omega = P X Q X R` and the 3-occurrence patterns are likewise unsettled. So are odd `r >= 5`, where padding does not apply. ∎

**Calibration.** Non-recursively-presented groups are not pattern-reducible
to `WP(H_M)`, because the pattern preimage of an r.e. set is r.e. This matches
Higman's theorem that only recursively presented groups embed in finitely
presented ones. At `r = 1`, Lemma E reproduces the fact that `WP(G) <= WP(H)`
by substitution holds for subgroups `G ≤ H`.
