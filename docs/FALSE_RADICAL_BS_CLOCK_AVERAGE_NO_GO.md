# The naive Baumslag--Solitar clock has macroscopic average carry

Date: 2026-08-11

## 1. Outcome

The exact clock representation in
`FALSE_RADICAL_BS_INTEGRAL_CYCLE_AMPLIFIER.md` contains a small phase
increment at one distinguished coordinate, but translating that increment
around the full cycle does not give a small normalized Hilbert--Schmidt
defect.

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

Thus the naive orbitwise clock has fixed normalized HS carry `sqrt(2)`.
It cannot by itself be the required low-defect/high-witness microstate.

The same obstruction holds for **every nontrivial character of the growing
`p`-primary clock sector**, not only for the primitive character above.  A
character of order `p^s` has translated squared carry equal to a fixed
positive `p`-th-root value when `s=1`, and exactly `2` when `s>=2`.
Consequently arbitrary orthogonal mixtures of full translated `p`-primary
clock orbits obey a dimension-independent marked-word domination bound.

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

There is a useful mixture consequence.  Take an orthogonal direct sum of
full translated primary-character blocks and let `eta` be the normalized
dimension occupied by nontrivial characters.  Then `(CNG17)` gives total
carry energy at least `c_p eta`.  If a marked unitary is the identity on
the trivial-character blocks, its squared normalized HS displacement is at
most `4 eta`.  Therefore every such model obeys

`marked squared displacement <=(4/c_p) carry energy`.   `(CNG19)`

Thus direct sums of these full-orbit diagonal blocks cannot have a
divergent relator-to-witness ratio, so the standard tensor-amplification
criterion has no suitable seed inside this ansatz.  Any successful
`p`-primary construction must change the orbitwise defect representative or
leave the orthogonal full-character-block model.

## 4. What the no-go rules out

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
4. cancellation after coupling to the square-zero relative module.

Each possibility requires an actual proof because the pairing lives in
the twisted coinvariants of `S-q`, not in ordinary cohomology of a circle.
In particular, the familiar fact that an ordinary flat circle connection
can be gauged onto one edge does not automatically apply.

## 5. Correct next finite problem

Let `T_M=S-q` on `I_M tensor R`, and let `chi` range over characters of
the cyclic cokernel `(CNG5)`.  The local quantitative question is to
compute, for the precise relation coordinates of the fold construction,

`inf_(allowed gauges b) (1/M)
   sum_j |Def_j(chi+(T_M)^*b)-1|^2`,                    `(CNG20)`

subject to a fixed lower bound on the marked fold-word displacement.

The words `allowed gauges`, `Def_j`, and `marked displacement` must be
derived from the actual square-zero elementary presentation.  Treating
`lambda_k(e_0-e_1)` alone as the defect loses the orbit average and leads
exactly to the false inference corrected here.

The most useful immediate target is therefore a sharp dichotomy:

> either exhibit a permitted gauge/model for which `(CNG11)=o(1)` and the
> marked displacement stays positive, or prove a uniform lower bound for
> every orbitwise diagonal character model.

Until that calculation is done, the local quantitative gate and the
global square-zero extension gate are both open.
