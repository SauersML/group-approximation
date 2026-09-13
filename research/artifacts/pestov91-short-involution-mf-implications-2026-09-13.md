# Explicit commuting involution relators implement monotone MF implications

2026-09-13. Written proof with finite matrix certificates; not
Lean-verified.

The [monotone-rule construction](pestov91-mf-closure-and-monotone-rules-2026-09-13.md)
used normal locally finite input subgroups. Here each input becomes
one explicit word in the three torsion generators. The output is
another explicit involution word, independent of all input words.
Short decoder certificates also improve the universal binary cylinder
word bound by a factor of 512.

## 1. Five short universal decoder words

Use the binary marking `(c,t,w)` from the unit-idempotent theorem and
write `C=c^{-1}`. All words in this table involve only `c,C,t`.

| Value | Word | Length |
| --- | --- | ---: |
| `e_12(1-p)` | `ctcctctctctctctCtC` | 18 |
| `e_12(p)` | `cctctcctcctccctcct` | 18 |
| `s_23` | `ctCtctcctCCt` | 12 |
| `s_13` | `ccctCCtCtctCtC` | 14 |
| `B=s_13 s_23` | `ccctcctCCtCtctcc` | 16 |

Here `s_ij` is the constant coordinate swap. These are identities
for every idempotent `p` in every unital `F_2`-algebra, including a
noncentral idempotent. All matrix entries lie in the image of
`F_2[p]/(p^2-p)`, so evaluation at `p=0` and `p=1` proves each identity.
The [finite certificate search](find-pestov91-short-decoder-2026-09-13.py)
verifies both evaluations exactly and records them in the
[decoder receipt](pestov91-short-decoder-receipt-2026-09-13.json).
It searches the 28,224-element group `SL_3(F_2)^2`.

The shorter transport word is

`V=s_23 w B w s_13=diag(u,u,u^{-2})`,                  (1)

and has length `12+1+16+1+14=44`. Multiplication of these monomial
matrices proves (1): their permutation is the identity and their
three diagonal weights are `u,u,u^{-2}`. Only the two-sided inverse
of `u` is used.

## 2. A 256-quadratic cylinder witness for every binary subshift

For a nonempty binary word `A` let `f_A` be its cylinder indicator.
The preceding table gives words `W_0,W_1` for `e_12(1-p),e_12(p)`.
Split any longer word into `AB` with
`a=|A|=floor(n/2)`, `b=|B|=ceil(n/2)`, and define

`W_(AB)=[s_23 W_A s_23,
         s_13 V^{-a} W_B V^a s_13]`.                 (2)

The two arguments are `e_13(f_A)` and `e_32(u^{-a}f_Bu^a)`.
Their commutator is `e_12(f_A u^{-a}f_Bu^a)=e_12(f_(AB))`.
This works at unequal child lengths and needs no padding symbols.

Let `L(n)` bound the expanded word length. The exact construction gives

`L(1)=18`,
`L(n)<=2L(a)+2L(b)+176a+104`.

An induction proves

`L(n)<=167n^2-100n-49<256n^2`.                         (3)

The bound at `n=1` is exactly 18. Substituting the induction bounds
on the two children leaves slack `12n+43` when `n` is even, and
`12n-36` when `n` is odd. The latter is nonnegative for every odd
`n>=3`, completing the proof. Thus for every nonempty binary subshift
`Z`, without minimality,

`W_A=1 in EL_3(R_Z) iff A does not occur in Z`,
`|W_A|<=2^8 |A|^2`.

Construction and full expansion take polynomial time. The improved
constant replaces the previous `2^17` bound for these new witnesses;
the older words are not being reinterpreted as shorter words.

## 3. A marker word normally generates exactly one edge factor

Use a binary-coded directed seam group `G_D`, with code length `ell`.
For an edge `e`, let `A_e` be the complete binary codeword of its unique
marker and set

`q_e=W_(A_e)`.

The delimiter `11` forces a codeword start at coordinate zero. The
unique marker then identifies one point in the isolated edge orbit.
Hence the cylinder of `A_e` is exactly that singleton, and `q_e` is
a nontrivial elementary transvection in the simple finitary factor
`L_e`. It is an involution and normally generates `L_e` in `G_D`.
Indeed its normal closure is contained in the normal factor `L_e`,
and simplicity makes its normal closure inside `L_e` equal to `L_e`.

For any nonempty finite edge set `J`, put `q_J=product_(e in J) q_e`.
Then

`normalClosure_(G_D)(q_J)=product_(e in J) L_e`.        (4)

For each chosen factor, commute `q_J` with a suitable element of
`L_e`. The other components commute away, and the resulting component
is nontrivial because `q_e` is noncentral. Simplicity gives that
whole factor. The opposite containment is immediate from normality.
This proves (4); it is what allows a variable with several occurrences
to be imposed by a single relation.

## 4. The word-level implication theorem

Given a positive Boolean formula `F` with `s` variable occurrences,
in which each named variable occurs, there is a LEF Kazhdan group
`G=<c,t,w>` and explicit words `a_1,...,a_m,b` such that:

- `c,t,w` have orders `7,2,2`;
- the words `a_1,...,a_m,b` are independent commuting involutions,
  generating `C_2^(m+1)` inside `G`;
- `b` is nontrivial in every quotient obtained by imposing any
  selection of the relations `a_i=1`;
- for every input set `I`,

  `[for every MF-target map phi:G->M,`
  ` (phi(a_i)=1 for all i in I) => phi(b)=1]`
  `iff F(1_I)=1`.                                    (5)

In (5), the left side means that **all** such maps kill `b`. When
`F(1_I)=0`, an explicit LEF quotient killing those inputs keeps `b`
nontrivial, and is injective on its entire simple normal closure.

For the construction, take the series/parallel network for the dual
formula and its feedback edge. Let `J_i` be the edges labeled by
variable `i`, let `e` be the feedback edge, and set

`a_i=q_(J_i)`, `b=q_e`.

The disjoint edge supports make these involutions independent and
commuting: any nonempty product has a nontrivial component in at
least one of the disjoint factors. Equation (4) identifies the normal
closure of the selected input words with the selected input subgroup
product. The prior monotone-rule theorem then proves (5), and also
shows that this product intersects `L_e` trivially. Thus the output
survives algebraically in every input quotient, even when all MF
images kill it.

The network has `s+1` edges including feedback and at most `s+1`
vertices. Its alphabet size `M` is at most `3s+3`, so with

`ell=2 ceil(log_2 M)+4`,

equation (3) gives the explicit total bound

`sum_i |a_i|+|b| <=256(s+1)ell^2=O(s log^2(s+2))`.     (6)

The construction uses one relation per named input, including variables
with repeated occurrences. To include an unused named variable in a
formula for a nonconstant monotone function, replace the formula by
its OR with the conjunction of all named variables; this preserves
the function and makes all variables occur.

Choose the same computable Sturmian system of slope `sqrt(2)-1` and
the mechanical point of intercept `1/2` at each vertex. Then `G` and
the explicit LEF counterquotients above have decidable word problem.
Their tagged languages are decidable: words without a marker must
have one vertex tag and be in its fixed endpoint language; a word with a marker has
one possible edge and alignment, checked against a computable seam.
Multiple markers are forbidden. Binary coding and the normal-form
algorithm preserve decidability. No language oracle is needed by the
word compiler itself.

All these groups have no nontrivial finite quotients. Thus the LEF
countertargets in the false cases of (5) are infinite. This is a
relative implication among homomorphisms out of `G`, not a finite
presentation of `G` or a universal implication over all groups.

## 5. Finite additions of involution relations

For `F=x_1 AND ... AND x_m`, the parallel-return construction gives
a particularly strong consequence: every proper selection of the
independent commuting involution relations `a_i=1` gives a LEF
quotient, while imposing all of them gives a just non-MF quotient.
The minimality here is among the designated individual relators.
For `m=1`, adding one involution relation already takes a three-generator
LEF Kazhdan group to a just non-MF group. Its normal kernel is the
infinite simple locally finite group normally generated by that word.

## 6. Compiler and validation

The [compiler](compile-pestov91-mf-implication-words-2026-09-13.py)
accepts a positive-formula JSON tree and outputs the source graph,
marker codes, and a shared straight-line word DAG. Every node records
its exact expanded length; no unused nodes are exported. The example
[input](pestov91-mf-word-example-input-2026-09-13.json) represents
`(x_0 AND x_1) OR (x_1 AND x_2)`, so it tests a repeated variable.
Its [generated word artifact](pestov91-mf-word-example-2026-09-13.json)
has 77 shared nodes. The input lengths are `20008,40016,20008` and the
output length is `20008`, totaling `100040` expanded letters, below
the bound `184320`. Words are kept compressed rather than materializing
long text.

The [matrix audit](check-pestov91-mf-implication-words-2026-09-13.py)
evaluates the actual exported DAG over finite cyclic `F_2` matrix
models. It checks each input and output against its expected cylinder
transvection, including a cycle carrying all marker codes, as well as
the involution, commutation and expanded-length identities. These
finite cyclic checks test the implementation. The general implication
theorem is the written argument above, using the prior graph radical
theorem. No Lean formalization or global priority assertion is claimed.

The final [matrix receipt](pestov91-mf-words-algebra-receipt-2026-09-13.json)
records a successful MSI run in 0.146425 seconds on five cycles of
period 15 and one of period 60. All output matrices, involution and
commutation identities, and recomputed word lengths passed. The
decoder search also completed in under one tenth of a second. The
matrix sizes and timings concern these finite certificates only.

Cairn 2.13.1 checked the four new graph nodes against snapshot
`19f0de970775c44ddde51c70ed60efe207abdf10` on MSI in 31.717 seconds.
`check --changed` and `preview` returned zero, both new claims were
`ESTABLISHED`, and neither baseline nor current graph had errors.
The graph contained 10,341 claims and 10,601 routes. The
[Cairn receipt](pestov91-words-cairn-receipt-2026-09-13.json) records
the source-delta and runner hashes. This paragraph and that receipt
were added after the run. Cairn validates dependencies, not the
mathematical proof; no Lean check was run.
