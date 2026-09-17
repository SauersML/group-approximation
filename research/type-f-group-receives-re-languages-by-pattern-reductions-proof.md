---
rg: 2
id: type-f-group-receives-re-languages-by-pattern-reductions-proof
kind: route
title: "Proof: compress the Boone configuration words by a Baumslag--Solitar stable letter and read the input's binary digits letter by letter"
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
Lean theorem. Steps 2 to 7 are paper proofs. The free-word identity of Step 4
and the Horner identity of Step 3 are also checked by the experiment.

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

`y` has infinite order in `G_M`, for three reasons:

- the base group `G = <t,x,y | [x,y]> = Z * Z^2` embeds in the tower `G'_M` (`boone-hnn-tower-embeds-base-group`);
- the tower embeds in `G_M`, which is an HNN extension of it;
- `y` generates a direct factor of `Z^2`.

So `y -> y` and `y -> y^m` (`m >= 2`) are both injective homomorphisms
`Z -> G_M`, and

    H_M = < G_M, s | s^-1 y s = y^m >

is an HNN extension. `G_M` embeds in it by Britton's lemma.

**Classifying space.** `boone-final-group-is-of-type-f` gives a finite
aspherical 3-complex `X` with `π1 X = G_M`. Take loops `γ_1` and `γ_2` in `X`
representing `y` and `y^m`, and glue a cylinder `S^1 × [0,1]` to `X` along
`γ_1` at one end and `γ_2` at the other. This is a graph of spaces with one
vertex space `X` and one edge space `S^1`. Both edge maps are π1-injective, so
the total space is aspherical (Scott--Wall, Proposition 3.6, the tool already
used in `boone-final-group-is-of-type-f-proof`) and its fundamental group is
`H_M`. It is a finite complex of dimension 3, so `H_M` is of type `F`.

**Presentation and r.e.** A finite presentation of `G_M`
(`boone-final-group-finitely-presented`), plus the letter `s` and one relator,
presents `H_M`. So `H_M` is finitely presented and `WP(H_M)` is r.e.
(`rePred_wordProblemPred` for that presentation code).

## Step 3. Horner compression

**Lemma H.** In any group where `s^-1 y s = y^m`, for all naturals
`d_0, ..., d_N`,

    Y(d_0 ... d_N) := y^{d_0} s^-1 y^{d_1} s^-1 ... s^-1 y^{d_N} s^N  =  y^{sum_i d_i m^i}.

*Proof.* By induction on `N`; `N = 0` is trivial. Write
`Y(d_0 ... d_N) = y^{d_0} s^-1 Y(d_1 ... d_N) s`, which is a free-word
identity: the inner word ends in `s^{N-1}`. By induction the inner word equals
`y^B` with `B = sum_{i >= 1} d_i m^{i-1}`, and `s^-1 y^B s = y^{m B}`. ∎

Hence `U(v) := x^{a_0} Y(d_0 ... d_N) = x^{a_0} y^{B(v)}` in `H_M`. This is the element
`rawSh (a_0, B(v))`, and `|U(v)| = a_0 + N + sum_i d_i + N = O(e_L + k l)`, with
constants depending only on `M`.

## Step 4. The pattern form

Let `rho(a)` be the product over `rev beta(a)` of `s^-1 y^{c_bit}`, let
`phi(a) = rho(a)^-1` (a fixed word) and `psi(a) = s^k`. Extend both
multiplicatively to monoid homomorphisms `A* -> F(gens H_M)`. Reading off the
digit list of Step 1, as an identity of free words after free reduction:

    Y(d_0 ... d_N) = y^{c_cons} s^-1 y^{c_1} · rho(v_{l-1}) ... rho(v_0) · s^-1 y^{c_0} (s^-1 y^{c_1})^{e_L} · s^{e_L + 2} · s^{k l}

and `rho(v_{l-1}) ... rho(v_0) = phi(v)^-1`, `s^{k l} = psi(v)`. So

    U(v) = C_1 · phi(v)^-1 · C_2 · psi(v),
    C_1 = x^{a_0} y^{c_cons} s^-1 y^{c_1},   C_2 = s^-1 y^{c_0} (s^-1 y^{c_1})^{e_L} s^{e_L + 2}.

`check_pattern_words.py` verifies this letter for letter, and Lemma H in the
faithful representation `y -> [[1,1],[0,1]]`, `s -> [[1/m,0],[0,1]]` of
`BS(1,m)`, on 3000 random instances (`results.txt`).

Put `U_0(X, Z) = C_1 X^-1 C_2 Z` and

    omega_L(X, Z) = k^-1 U_0^-1 t U_0 k U_0^-1 t^-1 U_0.

Then `W(v) := omega_L(phi(v), psi(v)) = k^-1 t(a_0,B(v)) k t(a_0,B(v))^-1` in
`H_M`, where `t(a_0,B) = u^-1 t u` and `u = x^{a_0} y^B`. This is the element of
`rawComm (a_0, B(v))`. Its length is `|omega_L| + 4 |phi(v)| + 4 |psi(v)|`,
linear in `l`, and a two-pass transducer writes it in linear time. The
`X^-1` needs one backward pass.

## Step 5. Correctness

`rawComm (a_0,B) = 1` in `G_M` iff `M.Halts (a_0,B)`
(`boone-commutator-criterion-for-halting`; in Lean
`commElt_eq_one_iff_halts` through `exists_boone_words`). `G_M` embeds in
`H_M` (Step 2), so the same holds in `H_M`. With Step 1:

    v ∈ L  <->  M.Halts (a_0, B(v))  <->  W(v) = 1 in G_M  <->  omega_L(phi(v), psi(v)) = 1 in H_M.

Only `omega_L` (through `e_L`) depends on `L`. `phi` and `psi` depend only on
`A`, `b` and `M`. For a finitely generated recursively presented group `G`
with generators `S`, `WP(G) ⊆ (S ∪ S^-1)*` is r.e., so it is an instance with
`A = S ∪ S^-1`. The letters `a` and `a^-1` get unrelated codes `b(a)` and
`b(a^-1)`, so `phi(a^-1) != phi(a)^-1` in general. ∎

## Step 6. Lemma E

Let `phi : (S ∪ S^-1)* -> F(T)` be a monoid homomorphism with
`phi(a^-1) = phi(a)^-1`, such that `v = 1` in `G = <S | R>` iff `phi(v) = 1`
in `H = <T | R'>`.

- `phi` induces a group homomorphism `F(S) -> F(T) -> H`.
- Every relator `r ∈ R` satisfies `r = 1` in `G`, hence `phi(r) = 1` in `H`. So the map factors through `G`.
- If `v` maps to `1` then `v = 1` in `G`, so the factored map is injective.

Conversely, an injective homomorphism `j : G -> H` with words `phi(a)`
representing `j(a)`, and `phi(a^-1) := phi(a)^-1`, satisfies
`phi(v) = j(v)`, so `phi(v) = 1 <-> v = 1`. ∎

## Step 7. The obstruction

Every inverse-respecting substitution is a pattern reduction:
`omega = X`, `psi` trivial. So every embedding gives a pattern reduction of
word problems, and every reducibility `R` containing pattern reductions
satisfies "`G <= H` implies `WP(G) <=_R WP(H)`". An obstruction through `R`
needs a `G` with `WP(G) not <=_R WP(H)` for every type `F_{n+1}` group `H`.

- If `G` is recursively presented, Step 5 gives `WP(G) <=_R WP(H_M)`, and `H_M` is of type `F`, hence of type `F_{n+1}`, by Step 2.
- If `G` is not recursively presented, then `WP(G)` is not r.e., so `G` embeds in no finitely presented group. The r.e. property already excludes it, and `R` adds nothing.

So `R` excludes nothing that the r.e. property does not exclude. By Lemma E,
at the finest end, inverse-respecting substitution, the relation "`WP(G) <= WP(H)`
for some `H` of type `F_{n+1}`" is the embedding question of Problem 1.1
verbatim. Any word-problem-reducibility obstruction must use a reducibility
strictly finer than two-homomorphism patterns and strictly coarser than
substitution. Otherwise it is either dead (Step 5) or circular (Lemma E). ∎

**Calibration.** Non-recursively-presented groups are not pattern-reducible to `WP(H_M)`, because the pattern preimage of an r.e. set is r.e.; this matches Higman's theorem that only recursively presented groups embed in finitely presented ones.
