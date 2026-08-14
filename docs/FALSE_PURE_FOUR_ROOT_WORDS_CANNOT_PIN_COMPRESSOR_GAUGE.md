# Pure four-root words cannot pin the compressor gauge

Date: 2026-08-14

## 1. Outcome

The proposed coefficient-identification gate cannot be proved from root
covariance plus the pure four-root associativity words alone. There is a
two-dimensional exact counterexample to any estimate of the form

```text
coproduct defect of compressor gauge
  <= f(four-root word defect),       f(0)=0.          (PFG1)
```

An exact intertwiner may be multiplied by a unitary in the source
commutant. This changes no covariance relation and no word formed solely
from root elements, but its group-like coproduct defect can be exactly one.

This does not kill the Leavitt/atlas program. The comb compressor is a
specific compiled word in the two finite charts, not a free HNN letter.
It does kill a tempting shortcut: pure Steinberg associativity cannot be
postprocessed into the coproduct defect of that word without using the word
decomposition or another mixed relation which detects its commutant gauge.

## 2. Exact covariance gauge freedom

Let `rho_0` and `rho_1` be unitary representations of a group `K`, and let
`U` be an exact intertwiner:

```text
U rho_0(k) U* =rho_1(k),       k in K.                (PFG2)
```

For every unitary

```text
C in rho_0(K)'                                       (PFG3)
```

the unitary `U'=UC` satisfies the same equations:

```text
U' rho_0(k) U'* =U C rho_0(k) C* U*
                 =U rho_0(k)U*
                 =rho_1(k).                          (PFG4)
```

The represented root elements are unchanged. Therefore every Steinberg
commutator, every nested four-root word, and both parenthesizations of root
multiplication are unchanged as well. In particular their associativity
energy remains exactly zero.

This is not merely a change of coordinates. In an HNN-style presentation
whose only relations involving the stable letter are `(PFG2)`, replacing
`U` by `UC` gives another exact representation of the same presentation.

## 3. A `C_2` gauge with coproduct defect one

Let `K=C_2={e,s}` and let `lambda_s` be its regular involution. Put

```text
p_+=(1+lambda_s)/2,
p_-=(1-lambda_s)/2,
C=p_+ + i p_-
  =[(1+i)/2] lambda_e+[(1-i)/2] lambda_s.             (PFG5)
```

The projections `p_+,p_-` are orthogonal and sum to one, so `C` is unitary.
Because `C_2` is abelian, `C` belongs to the commutant of its regular
representation. Thus it is an admissible gauge in `(PFG3)`.

For the group coproduct

```text
Delta(lambda_g)=lambda_g tensor lambda_g,             (PFG6)
```

the regular coefficients in `(PFG5)` have squared moduli `1/2`. The exact
Parseval formula from
`TRUE_COPRODUCT_DEFECT_PINS_COMMUTANT_GAUGE.md` gives

```text
||Delta(C)-C tensor C||_2^2
 =2-2 Re sum_g |c_g|^2 c_g
 =2-2 Re [(c_e+c_s)/2]
 =2-2(1/2)
 =1.                                                   (PFG7)
```

Hence the coproduct defect is exactly `1`, while the covariance and every
pure four-root word defect are exactly zero. This disproves `(PFG1)` even
for the smallest nontrivial finite commutant.

The example also shows why approximate functorial twirling does not finish
the problem. Since `UC` is already an exact intertwiner, its Fourier twirl
is `UC` itself. Twirling removes off-incidence mass; it cannot remove a
unitary acting inside an allowed incidence block.

## 4. Consequence for the current coproduct program

The uniform `30 delta` four-root telescope remains correct and useful, but
it cannot be the only input controlling the second coproduct defect. A
valid coefficient-identification theorem must include data that changes
when `U` is replaced by `UC`.

For the explicit atlas, the available such datum is the fixed source-word
formula for the comb compressor:

```text
u_src in A8 * A8,       reduced length 175.           (PFG8)
```

Its value is a polynomial in the two exact chart representations and their
relative position. Multiplying that value by an arbitrary commutant
unitary does not generally remain the value of the same word. Therefore
the source-word formula can in principle detect the gauge which covariance
alone cannot.

The correct positive target is consequently:

> **Compiled-word coproduct gate.** Evaluate `u_src` in a two-chart matrix
> microstate, construct its intrinsic homomorphism-twirled path blocks, and
> bound the genuine dual coproduct defect of that assembled coefficient
> operator using the fixed chart relators and the explicit factorization of
> `u_src`.

Pure root associativity may enter the proof after this construction, but it
cannot construct or identify the coefficient operator by itself.

## 5. Shortest falsification test for the compiled route

Before attempting a quantitative proof, test the following exact statement.
Let both `A_8` chart restrictions be finite regular representations with
arbitrary multiplicity and let their relative unitary vary. Evaluate the
literal 175-syllable word `u_src`. If there is a one-parameter relative
commutant gauge for which

1. all defining atlas relators remain exact;
2. the value of `u_src` changes by the gauge `C` in `(PFG5)` on a surviving
   multiplicity corner; and
3. the marked coefficient/Pauli sector remains nonzero,

then the compiled-word coproduct route is also locally sterile. If no such
deformation exists, the failed deformation equations identify the exact
mixed relators capable of pinning the gauge.

This is now the highest-signal finite calculation. It concerns a fixed word
and a fixed `C_2` phase path; it does not require a growing table, a large
numerical optimization, or a local build.

## 6. Status

The following implications remain valid:

```text
genuine coproduct defect -> classical gauge,
homomorphism covariance  -> intrinsic spectral paths,
four-root associativity  -> uniform table-size error budget. (PFG9)
```

What is false is the missing arrow

```text
pure four-root error -> genuine compressor coproduct defect. (PFG10)
```

That arrow must be replaced by a compiled-word or mixed-relator theorem.
No nonhyperlinear group is proved here.
