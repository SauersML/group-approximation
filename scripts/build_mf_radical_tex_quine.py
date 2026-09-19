#!/usr/bin/env python3
"""Build the exact TeX source quine and its Lean byte ledger."""

from __future__ import annotations

import argparse
from pathlib import Path


MARKER = "@@TEMPLATE_REPR@@"

TEMPLATE = r'''\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb,mathtools}
\usepackage[a4paper,margin=30mm]{geometry}
\usepackage[colorlinks=true,linkcolor=blue,urlcolor=blue]{hyperref}
\usepackage{listings}
\usepackage{microtype}

\lstset{
  basicstyle=\ttfamily\scriptsize,
  breaklines=true,
  breakatwhitespace=false,
  columns=fullflexible,
  keepspaces=true,
  showstringspaces=false
}

\newcommand{\RadMF}{\operatorname{Rad}_{\mathrm{MF}}}
\newcommand{\Qd}{\mathcal Q_{\mathbf d}}
\newcommand{\one}{\mathbf 1}

\title{A Source Quine in the Derived Operator--MF Residual}
\author{The \texttt{nonsofic\_existence} formalization}
\date{August 25, 2026}

\begin{document}
\maketitle

\begin{abstract}
We construct one fixed finitely presented non-MF group $U$ containing an
exact encoding of this manuscript, including the executable program printed
below.  The encoding is internal: for every source position $i$ and proposed
cell $b$, a word $W(i,b)$ belongs to
$[\RadMF(U),U]$ and
\[
  W(i,b)=\one \quad\Longleftrightarrow\quad
  b\text{ is the source cell at position }i.
\]
The cells are the file's literal bytes, followed by the sentinel $256$.
Thus the identity pattern of words lying in the operator--MF invisible part
recovers the complete file, not merely a hash or a semantic description.
The displayed Python program is a strict source quine: its standard output is
byte-for-byte this TeX file.  A Lean theorem proves the group-theoretic and
computability layers; an independent checker executes the quine, compares
bytes, and compares the generated Lean byte ledger with this file.
\end{abstract}

\section{The fixed invisible computer}

For a dimension sequence $\mathbf d=(d_n)$, put
\[
 \Qd=\prod_n M_{d_n}(\mathbb C)\big/\bigoplus_n M_{d_n}(\mathbb C),
\]
where the ideal is norm-null.  For a group $G$, define
\[
 \RadMF(G)=\bigcap_{\mathbf d}\ \bigcap_{\rho:G\to U(\Qd)}\ker\rho.
\]
An element is called operator--MF invisible when it belongs to this
intersection.

The formal development supplies a finitely presented group $E$ and an element
$z\in E$ such that
\[
 z\ne\one,\qquad z\in\RadMF(E),\qquad E\text{ is not operator--MF}.
\]
It also supplies one fixed finitely presented Boone controller $B$.  For every
partial-recursive program code $c$, there is an explicit controller word
$v_c\in B$ satisfying
\[
 v_c=\one\quad\Longleftrightarrow\quad c(0)\text{ is defined}.
\]
These are closed theorems in the repository, not hypotheses of the result in
this paper.

Define the fixed carrier
\[
 U=E*B
\]
and the faithful radical gate
\[
 R_c=[z,v_c]\in U.
\]
Here the letters denote their canonical free-factor images.  Free-product
normal forms give
\[
 [z,v_c]=\one\quad\Longleftrightarrow\quad v_c=\one,
\]
because $z\ne\one$ and the second input belongs to the other free factor.
Functoriality of the MF radical gives $z\in\RadMF(U)$, hence
\[
 R_c\in[\RadMF(U),U]\subseteq\RadMF(U).
\]
The same commutator is therefore simultaneously invisible and a faithful
readout of the controller.  This coupling is the point: the computation is
not stored in an unrelated direct factor or in an external label.

The group $U$ is finitely presented because both factors are.  It is non-MF
because it contains the non-MF factor $E$ and operator--MF is inherited by
subgroups.

\section{Output-sensitive words}

The domain detector $R_c$ alone records only a halting bit.  To encode source
data, fix a program $q$, a position $i$, and a proposed natural-number cell
$b$.  Let $t(q,i,b)$ be a partial-recursive program which runs $q(i)$ and
halts precisely when the returned value equals $b$.  Define
\[
 W_q(i,b)=R_{t(q,i,b)}.
\]

\paragraph{Output-query theorem.}
For every $q,i,b$,
\[
 W_q(i,b)\in[\RadMF(U),U]
 \quad\text{and}\quad
 W_q(i,b)=\one\Longleftrightarrow b\in\operatorname{eval}(q,i).
\]
The notation on the right is membership in a partial value: it means exactly
that $q(i)$ terminates with output $b$.

The proof is literal.  The filter $t(q,i,b)$ is obtained by composing the
universal evaluator with a partial equality acceptor.  The Boone compiler
turns its domain into $v_{t(q,i,b)}=\one$.  The faithful radical gate preserves
that equality truth value while placing the resulting word in the derived
MF residual.

If $q$ computes a total stream $s:\mathbb N\to\mathbb N$, then
\[
 W_q(i,b)=\one\Longleftrightarrow s(i)=b.                 \tag{1}
\]
For every wrong candidate $b\ne s(i)$, the word $W_q(i,b)$ is therefore a
\emph{nonidentity} element of $\RadMF(U)$.  Equation (1) is an exact equality
oracle, not an assertion that all encoding words collapse to the identity.

\section{The exact source quine}

The following Python 3 program is part of this TeX source.  Its first
assignment contains a quoted template, split into bounded physical lines, with
one distinguished token.  Replacing that token by the same deterministic
chunked representation reconstructs the program inside the same surrounding
manuscript.

% QUINE-PROGRAM-BEGIN
\begin{lstlisting}[language=Python]
TEMPLATE = @@TEMPLATE_REPR@@
def quote_chunks(text, width=72):
    return "(\n" + "".join(
        f"    {text[index:index + width]!r}\n"
        for index in range(0, len(text), width)
    ) + ")"
print(TEMPLATE.replace("@@TEMPLATE_REPR@@", quote_chunks(TEMPLATE), 1), end="")
\end{lstlisting}
% QUINE-PROGRAM-END

This is a source quine in the strict sense used here:
\[
 \operatorname{stdout}(\text{program above})
   =\text{the complete byte sequence of this file}.       \tag{2}
\]
No file is read, no network or environment input is consulted, and no
manuscript payload is appended by a wrapper.  The quoted template is the
program's own data, while the replacement operation installs that data's
representation at the unique self-reference site.  Equation (2) is checked
by executing the extracted program in an empty temporary working directory
and performing a byte comparison.

\section{Putting the whole manuscript in the invisible part}

Let $M$ be the literal byte list of this file and let $N=|M|$.  Define the
total source stream
\[
 s_M(i)=
 \begin{cases}
   M_i,&i<N,\\
   256,&i\ge N.
 \end{cases}
\]
All file cells lie in $\{0,\ldots,255\}$, so $256$ is an unambiguous end
sentinel.  A finite-list lookup is computable.  Universality of the
partial-recursive code language therefore yields a code $q_M$ with
\[
 \operatorname{eval}(q_M,i)=s_M(i)\qquad(i\in\mathbb N).
\]
Apply the output-query theorem to $q_M$ and set
\[
 \mathcal W_M=\{W_{q_M}(i,b):i\in\mathbb N, 0\le b\le256\}.
\]
Every member of $\mathcal W_M$ lies in $[\RadMF(U),U]$.  Starting at $i=0$,
the unique $b\le256$ for which $W_{q_M}(i,b)=\one$ is $s_M(i)$.  Emit it when
$b<256$ and stop when $b=256$.  This decoder recovers exactly $M$.

Combining this with (2), the decoded object is simultaneously the complete
manuscript and an executable program which outputs that same complete
manuscript.  In particular, the invisible encoding includes every byte of the
program's quoted template, both lines of its evaluator, every theorem
statement here, and the decoder description itself.

\paragraph{Finite realization.}
Although $\mathcal W_M$ is written as a total stream interface, the file is
finite.  Its complete content is determined by the finite family
\[
 \{W_{q_M}(i,b):0\le i\le N,\ 0\le b\le256\}.
\]
At $i=N$ the unique identity answer is the sentinel.  The infinite extension
only makes the source program total and does not hide any infinitary group
presentation: $U$ itself remains one fixed finite presentation.

\section{Why this is not a wrapper}

There are three distinct statements, and none is substituted for another.

First, the Python fixed point is syntactic and exact.  The checker compares
its output with the source bytes, not with a hash and not with a normalized
version of the TeX.

Second, those exact bytes are the data of a computable stream compiled into
the Boone factor.  The observable words are not the controller words alone:
they are commutators with the nonidentity radical mark.  The free-product gate
proves that this mixing preserves the output truth table exactly, while
radical functoriality proves that every mixed word is invisible to every
matrix-corona representation.  Wrong byte guesses give nontrivial invisible
elements, so the encoding has genuine internal contrast.

Third, self-reference is not advertised as the analytic source of non-MF.
The carrier depends on the independently proved non-MF seed $E$.  The quine
adds exact computation and self-description inside its MF residual; it does
not reprove the seed obstruction.  This separation avoids the circular claim
that a manuscript declaring its group non-MF somehow makes the group non-MF.

Thus the construction is stronger than juxtaposing a non-MF group with a
quine, but narrower than a self-certifying analytic obstruction.  Its precise
content is an exact source fixed point whose complete equality oracle lives in
the derived MF-invisible subgroup of a closed, finitely presented non-MF
carrier.

\section{Formal and executable custody}

The Lean module
\texttt{GroupApproximation.Computability.MFRadicalQuine} proves:
\begin{itemize}
\item partial recursiveness of the output equality filter;
\item $W_q(i,b)\in[\RadMF(U),U]$ and operator--MF invisibility;
\item $W_q(i,b)=\one$ exactly when $q(i)$ returns $b$;
\item existence of an invisible source encoding for every computable stream.
\end{itemize}

The generated module
\texttt{GroupApproximation.Computability.MFRadicalQuineSource} contains the
literal natural-number list of this file's bytes, defines the sentinel stream,
proves that stream computable, and instantiates the invisible-source theorem.
The list is generated only after the TeX fixed point is complete, so it is a
custody ledger rather than an assumption used to manufacture the quine.

The independent checker
\begin{center}
\path{scripts/check_mf_radical_tex_quine.py}
\end{center}
performs four checks:
\begin{enumerate}
\item regenerate the fixed point from the canonical template;
\item extract and execute the embedded source program;
\item compare both results byte-for-byte with this file;
\item parse the Lean byte ledger and compare every integer with the same file.
\end{enumerate}
The Lean build then checks the group-theoretic theorem and the concrete source
instantiation with the kernel.

\section{Conclusion}

One fixed finitely presented non-MF group $U$ now carries a complete source
quine internally in its derived MF residual.  The construction has two exact
fixed points: a syntactic fixed point producing the TeX bytes, and a faithful
group-theoretic gate turning output equality into identity while retaining
MF invisibility.  Their interface is the literal source-cell stream, verified
independently and formalized as a computable object.

\end{document}
'''


def quine_bytes() -> bytes:
    if TEMPLATE.count(MARKER) != 2:
        raise RuntimeError("the marker must occur once as code and once as data")
    # Replace only the code-position occurrence.  The second occurrence is the
    # string literal used by the running quine and must remain literal.
    source = TEMPLATE.replace(MARKER, quote_chunks(TEMPLATE), 1)
    return source.encode("ascii")


def quote_chunks(text: str, width: int = 72) -> str:
    return "(\n" + "".join(
        f"    {text[index:index + width]!r}\n"
        for index in range(0, len(text), width)
    ) + ")"


def lean_source(data: bytes) -> str:
    rows = []
    for start in range(0, len(data), 20):
        chunk = ", ".join(str(value) for value in data[start : start + 20])
        rows.append("  " + chunk)
    byte_rows = ",\n".join(rows)
    return f'''import GroupApproximation.Computability.MFRadicalQuine

/-!
# Exact byte ledger for `mf_radical_tex_quine.tex`

This file is generated from the final TeX fixed point.  The independent quine
checker compares this list cell-for-cell with the manuscript before the Lean
kernel checks the computable-stream instantiation below.
-/

namespace GroupApproximation
namespace MFRadicalQuineSource

open MFRadicalQuine MFRadicalComputer

noncomputable section

-- MANUSCRIPT-BYTES-BEGIN
def manuscriptBytes : List ℕ := [
{byte_rows}
]
-- MANUSCRIPT-BYTES-END

def eof : ℕ := 256

def manuscriptCell (i : ℕ) : ℕ :=
  (manuscriptBytes[i]?).getD eof

theorem computable_manuscriptCell : Computable manuscriptCell := by
  exact Computable.option_getD
    (Computable.list_getElem?.comp (Computable.const manuscriptBytes)
      Computable.id)
    (Computable.const eof)

theorem manuscript_invisible_source_encoding :
    ∃ q : Nat.Partrec.Code,
      ComputesStream q manuscriptCell ∧
      (∀ i b, NormMFInvisible (outputWord q i b)) ∧
      (∀ i b, outputWord q i b ∈
        ⁅normMFResidual Carrier, (⊤ : Subgroup Carrier)⁆) ∧
      (∀ i b, outputWord q i b = 1 ↔ manuscriptCell i = b) :=
  exists_invisible_source_encoding manuscriptCell computable_manuscriptCell

end

end MFRadicalQuineSource
end GroupApproximation
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit-tex", type=Path)
    parser.add_argument("--emit-lean", type=Path)
    parser.add_argument("--tex", type=Path)
    args = parser.parse_args()

    data = quine_bytes()
    if args.emit_tex is not None:
        args.emit_tex.write_bytes(data)
    if args.emit_lean is not None:
        if args.tex is None:
            raise SystemExit("--emit-lean requires --tex")
        actual = args.tex.read_bytes()
        if actual != data:
            raise SystemExit("refusing to ledger a TeX file that is not the fixed point")
        args.emit_lean.write_text(lean_source(actual), encoding="utf-8")
    if args.emit_tex is None and args.emit_lean is None:
        raise SystemExit("choose --emit-tex and/or --emit-lean")


if __name__ == "__main__":
    main()
