# LEF Burnside groups and limits of finite simple groups: literature pins

Lane hl-lef-burnside, 2026-09-13. The TeX sources below were fetched from arXiv on MSI into
`/scratch.global/sauer354/hl-lef-burnside/src/` and read there. Line numbers refer to those files.

## Bradford, "Quantifying local embeddings into finite groups" (arXiv:2104.07111)

File `LEF_Growth_in_General_v2.tex`, l.1676–1682:

> Next, it is not known whether infinite free Burnside groups are LEF.
> Indeed it is known that either free Burnside groups
> of sufficiently large odd exponent
> are locally embeddable into the class $\mathcal{S}$
> of nonabelian finite simple groups,
> or there is a non-residually finite hyperbolic group
> (see Subsection 5.4 of \cite{Capr} for a discussion).

`\cite{Capr}` (l.1797–1801) is Caprace, "Finite and infinite quotients of finite and indiscrete
groups", Groups St Andrews 2017 in Birmingham, CUP 2019; arXiv:1709.05949 below.

## Caprace, "Finite and infinite quotients of discrete and indiscrete groups" (arXiv:1709.05949)

File `Quotients_arXiv_31may18.tex`.

- **Problem `prob:limits`** (begins l.1299):

  > \begin{enumerate}[(i)]
  > \item Find an algebraic characterization of the  limits of non-abelian finite simple groups in the space of marked groups.
  > \item Can an infinite group of finite exponent be a limit of non-abelian finite simple groups?
  > \end{enumerate}

  It is followed by: "A  more precise version of Problem~\ref{prob:limits}(ii) is proposed by
  Ivanov--Olshanskii in \cite[Problem~2]{IvanovOlshanskii}." The reference (l.1765–1768) is
  Ivanov and Ol'shanskii, "Hyperbolic groups and their quotients of bounded exponents",
  Trans. AMS 348 (1996), 2091–2138. That paper was **not** read.
- **Corollary `cor:Olsh4`** (l.1241): "If all hyperbolic groups are residually finite, then for every
  non-elementary hyperbolic group $G$ with $E_G(G)= \{1\}$, every finite subset $M \subset G$ and
  every $n \geq 5$, there is a homomorphism $\rho \colon G \to Q$ of $G$ onto a finite simple group
  $S$ containing a subgroup isomorphic to $\Alt(n)$, and such that the restriction of $\rho$ to $M$
  is injective."
- **Corollary `cor:Olsh5`** (l.1344): "If all hyperbolic groups are residually finite, then for every
  non-elementary hyperbolic group $G$ with $E_G(G) = \{1\}$, every $d$-generator marking $(G,S)$ is
  a limit a non-abelian finite simple groups (containing arbitrarily alternating groups) in the
  space of $d$-generated marked groups."
- **Remark after it** (l.1348): "A crucial  point to underline is that, in the space of marked
  groups, limits of hyperbolic groups can be quite wild: they can be infinite groups of finite
  exponent by \cite{IvanovOlshanskii}. Thus, if all hyperbolic groups were residually finite, then
  Burnside groups would arise as limits of non-abelian finite simple groups."
- **Proposition `prop:Cor`** (Cornulier, l.1315): "For any prime $p$, the wreath product
  $C_p \wr \mathbf Z$ is a limit of alternating groups of prime degrees in the space of marked
  groups." Caprace notes this answers positively whether a limit of non-abelian finite simple groups
  can satisfy a law.

**Not checked here.** Whether the Coulon stages of `free-burnside-is-a-limit-of-hyperbolic-groups`
satisfy $E_{G_k}(G_k) = \{1\}$, which `cor:Olsh5` needs. The repo's route to the same
consequence (clause 4 of `lef-burnside-groups-iff-finite-simple-limits`) does not use it.

## Arzhantseva–Cherix, "Quantifying metric approximations of groups" (arXiv:2008.12954)

File `mprofile.tex`, l.2169–2171:

> \begin{conjecture}\cite[Conjecture 2.8]{arzhantseva_approx_2012}
> All Gromov hyperbolic groups are residually finite $\Longleftrightarrow$ all Gromov hyperbolic groups are sofic.
> \end{conjecture}

## Consequence for the repo

- The LEF form of the Burnside problem (`large-odd-exponent-lef-burnside-groups-are-finite`) is
  open in the literature (Bradford).
- Through `lef-burnside-groups-iff-finite-simple-limits`, it is equivalent at each exponent to
  Caprace's Problem `prob:limits`(ii).
