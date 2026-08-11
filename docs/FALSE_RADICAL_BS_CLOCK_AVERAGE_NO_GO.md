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

## 3. What the no-go rules out

Suppose a proposed relation defect is the diagonal matrix whose `j`th
entry is `delta_(k,j)-1`.  Its normalized Hilbert--Schmidt norm squared is
exactly the left side of `(CNG4)`, hence equals `2`.  Any construction that
uses all translated adjacent quotients with uniform multiplicity has the
same obstruction.

The calculation does **not** rule out:

1. changing the representative by an allowed twisted gauge and
   concentrating the defect on `o(M)` coordinates;
2. replacing the diagonal orbitwise character by a non-diagonal model;
3. using a different character of the full cyclic group `(CNG5)`;
4. cancellation after coupling to the square-zero relative module.

Each possibility requires an actual proof because the pairing lives in
the twisted coinvariants of `S-q`, not in ordinary cohomology of a circle.
In particular, the familiar fact that an ordinary flat circle connection
can be gauged onto one edge does not automatically apply.

## 4. Correct next finite problem

Let `T_M=S-q` on `I_M tensor R`, and let `chi` range over characters of
the cyclic cokernel `(CNG5)`.  The local quantitative question is to
compute, for the precise relation coordinates of the fold construction,

`inf_(allowed gauges b) (1/M)
   sum_j |Def_j(chi+(T_M)^*b)-1|^2`,                    `(CNG11)`

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
