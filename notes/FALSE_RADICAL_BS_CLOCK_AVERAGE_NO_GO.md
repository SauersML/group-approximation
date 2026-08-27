# The translated clock increment is macroscopic, not a small carry

Date: 2026-08-11

## 1. Outcome

The exact clock representation in
`FALSE_RADICAL_BS_INTEGRAL_CYCLE_AMPLIFIER.md` contains a small phase
increment at one distinguished coordinate, but translating that increment
around the full cycle does not give a small normalized Hilbert--Schmidt
quantity.  Whether that quantity is a defect or a witness depends on the
extension.  For the natural two-sector fold it is the desired witness,
while the Baumslag--Solitar relator is exact.

Fix an odd prime `p`, put `q=1+p`, and let `M=p^k`.  For the character

`lambda_k(e_j)=q^j/p^(k+1) mod Z`,                       `(CNG1)`

the translated adjacent quotient is

`delta_(k,j)`
` =exp(2 pi i(lambda_k(e_j)-lambda_k(e_(j+1))))`
` =exp(-2 pi i q^j/p^k)`.                              `(CNG2)`

The distinguished value `delta_(k,0)=exp(-2 pi i/p^k)` tends to `1`.
Nevertheless, for every `k>=2`,

`(1/M) sum_(j=0)^(M-1) delta_(k,j)=0`,                 `(CNG3)`

and hence

`(1/M) sum_(j=0)^(M-1) |delta_(k,j)-1|^2=2`.           `(CNG4)`

Thus the translated increment has fixed normalized HS size `sqrt(2)`.  It
cannot be cited as a vanishing averaged carry.  On the other hand, for the
two exact sectors `H_k` and `H_k^q` it equals the marked fold displacement,
so it is positive rather than obstructive.

The same obstruction holds for **every nontrivial character of the growing
`p`-primary clock sector**, not only for the primitive character above.  A
character of order `p^s` has translated squared carry equal to a fixed
positive `p`-th-root value when `s=1`, and exactly `2` when `s>=2`.
Consequently, **if** these translated phases are used as relation defects,
arbitrary orthogonal mixtures of full translated `p`-primary clock orbits
obey a dimension-independent marked-word domination bound.  This
conditional clause matters: in the exact local `B` block the same phases
are fold-word eigenvalues instead.

This corrects only the quantitative interpretation.  It does not affect
the exact calculation

`H_1(B,I_M) ~= Z/((q^M-1)/(q-1))Z`,                    `(CNG5)`

the explicit generator, its exact `p^k`-primary order, or the exact
relation `C_k H_k C_k^(-1)=H_k^q`.

## 2. Distribution of the translated increments

For odd `p`, the class `q=1+p` has order `p^(k-1)` in

`(Z/p^k Z)^times`                                      `(CNG6)`

when `k>=2`.  Indeed, the lifting-the-exponent formula gives

`v_p(q^n-1)=1+v_p(n)`.                                 `(CNG7)`

Therefore the powers `q^j`, for `0<=j<p^k`, run through every element of

`1+p Z / p^k Z`                                        `(CNG8)`

exactly `p` times.  Writing these elements as `1+p a`, with
`0<=a<p^(k-1)`, gives

`sum_(j=0)^(p^k-1) exp(-2 pi i q^j/p^k)`
` =p exp(-2 pi i/p^k)
     sum_(a=0)^(p^(k-1)-1) exp(-2 pi i a/p^(k-1))`
` =0`.                                                  `(CNG9)`

This proves `(CNG3)`.  Since `|z-1|^2=2-2 Re(z)` on the unit circle,
`(CNG4)` follows immediately.

For `k=1`, all powers satisfy `q^j=1 mod p`, so the energy is the fixed
positive number

`|exp(-2 pi i/p)-1|^2`;                                `(CNG10)`

there is no vanishing sequence in that case either.

## 3. All p-primary clock characters have a uniform gap

Let

`y=e_0-e_1 in I_M`, `M=p^k`.                            `(CNG11)`

Theorem 1 of `FALSE_RADICAL_BS_INTEGRAL_CYCLE_AMPLIFIER.md` identifies the
`p`-primary part of the class of `y` with a generator of `C_(p^k)`.  In the
coinvariants of `S-q`,

`S^j y=q^j y`.                                          `(CNG12)`

Let `chi` be a character whose restriction to this primary component has
exact order `p^s`, `1<=s<=k`.  For a unit `a mod p`, orient the generator so
that

`chi(y)=exp(2 pi i a/p^s)`.                             `(CNG13)`

Its translated carry phases are therefore

`delta_(chi,j)=chi(S^j y)=exp(2 pi i a q^j/p^s)`.       `(CNG14)`

**Theorem 1 (uniform full-orbit p-primary gap).**  The normalized squared
carry energy

`E_M(chi)=(1/M)sum_(j=0)^(M-1)|delta_(chi,j)-1|^2`      `(CNG15)`

satisfies

`E_M(chi)=|exp(2 pi i a/p)-1|^2` if `s=1`,
`E_M(chi)=2` if `s>=2`.                                 `(CNG16)`

In particular every nontrivial `p`-primary character satisfies

`E_M(chi)>=c_p`,
`c_p=min(2,4 sin(pi/p)^2)>0`.                           `(CNG17)`

**Proof.**  For `s=1`, `q=1 mod p`, so every term in `(CNG14)` equals the
same primitive `p`-th root.  For `s>=2`, the powers of `q` modulo `p^s` run
through `1+pZ/p^sZ` exactly `p^(k-s+1)` times.  Hence

`(1/M)sum_j delta_(chi,j)`
` =exp(2 pi i a/p^s)`
`   (1/p^(s-1))sum_(r=0)^(p^(s-1)-1)`
`      exp(2 pi i a r/p^(s-1))`
` =0`.                                                   `(CNG18)`

The identity `|z-1|^2=2-2 Re(z)` proves `(CNG16)`.  Minimizing the
`s=1` value over `a` gives `(CNG17)`.  End proof.

There is a useful conditional mixture consequence.  Suppose the phases
in `(CNG14)` occur as relation defects.  Take an orthogonal direct sum of
full translated primary-character blocks and let `eta` be the normalized
dimension occupied by nontrivial characters.  Then `(CNG17)` gives total
carry energy at least `c_p eta`.  If a marked unitary is the identity on
the trivial-character blocks, its squared normalized HS displacement is at
most `4 eta`.  Therefore every such model obeys

`marked squared displacement <=(4/c_p) carry energy`.   `(CNG19)`

Thus direct sums of these full-orbit diagonal blocks cannot have a
divergent relator-to-witness ratio **under that defect identification**.
The theorem does not say that every occurrence of `(CNG14)` is a relator
defect.

## 4. The exact local fold block

Let `H_k,C_k` be the clock and shift matrices from `(ICA24)`.  Put

`H_k^(1)=H_k`, `H_k^(2)=H_k^q`.                       `(CNG21)`

Both pairs `(H_k^(i),C_k)` satisfy

`C_k H_k^(i) C_k^(-1)=(H_k^(i))^q`                   `(CNG22)`

exactly.  The marked fold between the two translation generators is

`H_k^(2)(H_k^(1))^(-1)=H_k^(q-1)=H_k^p`.             `(CNG23)`

Its `j`th eigenvalue is the complex conjugate of `delta_(k,j)`.  Therefore
`(CNG4)` gives

`||H_k^p-I||_(2,normalized)^2=2`                      `(CNG24)`

for every `k>=2`.  Hence the frozen clock/shift block already has zero
`B`-relator defect and macroscopic local fold displacement.

It is not yet a representation of the amalgamated double: no common
`Gamma` sector or square-zero elementary covariance has been constructed.

## 5. What the no-go rules out

Suppose a proposed relation defect is the diagonal matrix whose `j`th
entry is `delta_(k,j)-1`.  Its normalized Hilbert--Schmidt norm squared is
exactly the left side of `(CNG4)`, hence equals `2`.  Any construction that
uses all translated adjacent quotients with uniform multiplicity has the
same obstruction.

The calculation and Theorem 1 do **not** rule out:

1. changing the representative by an allowed twisted gauge and
   concentrating the defect on `o(M)` coordinates;
2. replacing the diagonal orbitwise character by a non-diagonal model;
3. using a character whose decisive component is outside the growing
   `p`-primary sector of `(CNG5)`; or
4. cancellation after coupling to the square-zero relative module; or
5. using `(CNG4)` as the marked fold energy, as in `(CNG21)--(CNG24)`.

Each possibility requires an actual proof because the pairing lives in
the twisted coinvariants of `S-q`, not in ordinary cohomology of a circle.
In particular, the familiar fact that an ordinary flat circle connection
can be gauged onto one edge does not automatically apply.

## 6. Correct next finite problem

Let `T_M=S-q` on `I_M tensor R`, and let `chi` range over characters of
the cyclic cokernel `(CNG5)`.  The remaining quantitative question is to
compute, for the precise **additional** relation coordinates of the full
fold construction,

`inf_(allowed gauges b) (1/M)
   sum_j |Def_j(chi+(T_M)^*b)-1|^2`,                    `(CNG20)`

subject to the fixed lower bound `(CNG24)` on the marked fold word.

The words `allowed gauges` and `Def_j` must be derived from the actual
square-zero elementary presentation.  The `BS(1,q)` relator is not among
these defects: it vanishes exactly by `(CNG22)`.  Treating
`lambda_k(e_0-e_1)` alone as a small amalgam or covariance defect loses the
orbit average and leads exactly to the false inference corrected here.

The most useful immediate target is therefore a sharp dichotomy:

> either exhibit a permitted gauge/model for which `(CNG20)=o(1)` and the
> marked displacement stays positive, or prove a uniform lower bound for
> every orbitwise diagonal character model.

The clock block itself passes the local `B` test.  Until `(CNG20)` is
computed, the square-zero/amalgam extension gate remains open.
