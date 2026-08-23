# A proof-triggered MF-radical switch and the exact status of the reverse-Kleene compiler

Date: 2026-08-23.

This note closes the bare threshold-free operator-norm compiler interface and
separates that closure from the stronger, genuinely seed-free support-profile
programme.

## 1. Marked seed

Fix a finitely presented group

```text
H=<A|Q>
```

and a word `z` on `A` whose image in `H` satisfies

```text
z!=1,
z in Res_MF(H).
```

The literal group `E` and its central mark `w` provide such a pair by
`literal-central-mark-corona-invisible`. Nothing below uses centrality,
torsion, property (T), or the particular construction of the seed.

## 2. The halting-sensitive switch compiler

Given a Turing-machine index `e`, use the finite alphabet

```text
S_e=A disjoint_union {s}
```

and the marked word `w_e=z`. The relator enumerator emits every relator in
`Q` immediately, simulates `e`, and emits the one extra relator

```text
s=1
```

if and only if `e` halts. This is a total computable compiler to uniformly
recursively enumerable ordinary group presentations.

Let `Gamma_e=<S_e|R_e>`.

### HALT branch

If `e` halts, then

```text
Gamma_e = <A,s | Q,s> ~= H.
```

The isomorphism kills `s` and fixes the `A`-letters. Therefore the marked
word is still `z`, hence is nontrivial.

### NONHALT branch

If `e` does not halt, no relator involving `s` is ever emitted, so

```text
Gamma_e = <A,s | Q> ~= H * <s> ~= H * Z.
```

The canonical free-factor map `i:H->H*Z` is injective. Functoriality of the
MF radical gives

```text
i(z) in Res_MF(H*Z).
```

Thus this one-generator switch satisfies exactly the threshold-free compiler
semantics

```text
e halts     => w_e!=1 in Gamma_e,
e nonhalts  => w_e in Res_MF(Gamma_e).
```

No matrix code, dimension oracle, support-profile authentication, terminal
challenge, or quantitative defect threshold enters.

## 3. Reverse Kleene becomes an unconditional self-aware proof

Feed this compiler to `threshold-free-reverse-kleene-mf-higman`. The fixed
program enumerates finite proofs that its own compiled word is trivial.
Kleene's recursion theorem supplies an index `e_*` for that program.

If `e_*` halted, its proof search would certify `w_(e_*)=1`, while the HALT
semantics above identify the compiled group with `H` and say the same word is
nontrivial. Hence `e_*` does not halt. The NONHALT semantics therefore put
`w_(e_*)` in the MF radical. The same proof-enumeration argument shows
`w_(e_*)!=1`. Consequently `Gamma_(e_*)` is non-MF.

For this particular compiler the source group is already finitely presented:

```text
Gamma_(e_*) ~= H*Z.
```

The effective Higman step is unnecessary, although the abstract theorem
remains useful for other recursively presented compilers.

This is a genuine proof-theoretic self-reference construction: the fixed
program determines which presentation branch occurs by searching for a proof
about the marked word of that very branch. It is not an independent analytic
source of non-MF-ness; the invisible seed `z` carries the obstruction.

## 4. Exact equivalence of the bare compiler interface and a marked non-MF seed

Consider the following two existence statements.

```text
(SEED) There is a finitely presented H and z!=1 in Res_MF(H).
(COMP) There is a total computable threshold-free compiler satisfying TFM1--TFM2.
```

Then `(SEED)` and `(COMP)` are equivalent.

- `(SEED)=>(COMP)` is the switch compiler above.
- `(COMP)=>(SEED)` is the reverse-Kleene theorem followed by effective Higman.
  The fixed-point word is nontrivial and MF-invisible in the recursively
  presented group. Its image under the Higman embedding remains nontrivial
  and remains in the MF radical by functoriality.

Therefore the bare compiler interface is not a strictly earlier route to the
first non-MF group. It is an exact repackaging of a marked MF-radical seed.
Any claim of a *seed-free* compiler must include constructional information
beyond the extensional clauses TFM1--TFM2.

## 5. Monotone positive-branch barrier

The switch also exposes a general obstruction. Suppose a compiler has a
nonhalting presentation `Gamma_infty`, and halting only appends relators, so
there is a quotient map

```text
q:Gamma_infty -> Gamma_halt
```

carrying the nonhalting mark `w` to the halting mark. If

```text
w in Res_MF(Gamma_infty)
```

then functoriality gives

```text
q(w) in Res_MF(Gamma_halt).
```

Consequently, if `q(w)!=1`, the halting group is itself non-MF. In
particular no monotone append-on-halt compiler can simultaneously have

```text
NONHALT: w in Res_MF,
HALT:    w survives and Gamma_halt is MF.
```

A genuinely seed-free positive branch would need a nonmonotone compilation
architecture or a different semantic interface; ordinary r.e. relator
addition cannot provide it.

## 6. Prime-coded literal self-awareness

There is also a finite-presentation family which makes the compiler index
visible without changing the obstruction. Let `p_e` be the `(e+1)`-st prime
and put

```text
Gamma_e=H*C_(p_e),
w_e=z.
```

Free-product normal form preserves `z!=1`, and MF-radical functoriality
preserves its invisibility. The cyclic factor records `e` in one finite
relator while the semantic carrier is constant. Thus the fixed-point program
may literally print a presentation containing its own prime code. This is a
Gödel-coded presentation of the seeded construction, not an independent
analytic obstruction.

## 7. Machine-checked logical core

`GroupApproximation/Computability/SeededSelfAwareMFCompiler.lean` checks:

- transport of a marked invisible seed through free products;
- the constant-carrier and proof-triggered endpoint semantics;
- the proposition-level reverse-Kleene contradiction
  `halts <-> mark=1`, `HALT -> mark!=1`, `NONHALT -> invisible`;
- equivalence between one marked MF-radical seed and the resulting logical
  self-aware compiler endpoint;
- the prime-coded free-product carrier and preservation of the mark;
- the monotone same-mark no-go: if an invisible mark survives a quotient, the
  quotient cannot be operator MF.

The effective recursion theorem, enumeration of recursively enumerable group
proofs, and presentation coding remain represented by Cairn's computability
nodes rather than a Lean machine-code structure. The formal theorem is named
`logicalSelfAwareMFCompiler_iff_seed` to keep that boundary explicit.
The Lean carrier is parameterized by the code function; the effective layer
instantiates it with the `(e+1)`-st-prime function.

## 8. Consequences for the Cairn graph

1. `authenticated-opnorm-challenge-compiler` is established **as stated** by
   the marked switch, using the literal invisible mark as seed.
2. `reverse-kleene-support-profile-nonmf` is established as a self-aware
   non-MF construction, but not as an independent support-profile proof.
3. `authenticated-opnorm-compiler-assembly`,
   `opnorm-support-profile-challenge-library`, and
   `opnorm-depthwise-same-mark-return` remain meaningful only as a stronger
   seed-free implementation programme. They are no longer prerequisites for
   the unconditional self-aware endpoint.
4. The proof-theoretic branch of
   `self-aware-finite-approximation-trichotomy` must distinguish seeded
   self-reference from a seed-free detector compiler.
