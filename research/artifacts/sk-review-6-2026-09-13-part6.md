# sk-review-6, part 6: the Odifreddi p. 462 locator for Sacks' continuum antichain (queue entry 8) (2026-09-13)

Lane sk-verify-6.
- **Request (sk-free-7, `research/artifacts/sk-free-7-proposal-2026-09-13.md`):** confirm that Odifreddi, *Classical Recursion Theory* (1989), p. 462 states Sacks' continuum antichain of Turing degrees, as cited by Terwijn arXiv:math/0606529 l.459. Give the exact theorem number and the bibliographic data.
- **Proposed note text:** "The Turing degrees contain an antichain of size continuum~\cite[p.~462]{Odifreddi}". Proposed bibitem: "P.~Odifreddi, \emph{Classical Recursion Theory}, North-Holland, Amsterdam, 1989."

## Verdict: PARTIAL. Bibliographic data PASS; p. 462 confirmed only secondarily; theorem number NOT obtained

### 1. Terwijn's citation (read at source)
arXiv:math/0606529 v1 (submitted 21 Jun 2006, "On the structure of the Medvedev lattice"), e-print `structure.tex`:
- l.458–461: "We construct an antichain of size $2^{\aleph_0}$ as in Sacks' construction of such an antichain in the Turing degrees \cite[p462]{Odifreddi} by constructing a tree of $\C_\alpha$, $\alpha\in 2^\omega$, …"
- l.1150–1152: "Let $\{f_\alpha: \alpha< 2^\omega\}$ be a set of pairwise Turing incomparable elements of $\mbox{}^\omega 2$, which exists by a result of Sacks, cf.\ \cite{Odifreddi}."
- l.1651–1654, bibitem: "Piergiorgio Odifreddi, \textit{Classical recursion theory}, Vol. 1, Studies in logic and the foundations of mathematics Vol. 125, North-Holland, 1989."

So the page locator comes from a printed citation by a recursion theorist, and it refers to Volume I.

### 2. Where p. 462 sits in the book (Crossref, Elsevier deposit, ISBN 978-0-444-89483-0, the 1992 paperback printing of Vol. I)

| pages | chapter | DOI |
|---|---|---|
| 1–16 | Introduction | 10.1016/s0049-237x(08)70018-1 |
| 17–123 | Chapter I Recursiveness and Computability | 10.1016/s0049-237x(08)70019-3 |
| 125–249 | Chapter II Basic Recursion Theory | 10.1016/s0049-237x(08)70020-x |
| 251–360 | Chapter III Post's Problem and Strong Reducibilities | 10.1016/s0049-237x(08)70021-1 |
| 361–445 | Chapter IV Hierarchies and Weak Reducibilities | 10.1016/s0049-237x(08)70022-3 |
| **447–553** | **Chapter V Turing Degrees** | **10.1016/s0049-237x(08)70023-5** |
| 555–601 | Chapter VI Many-One and Other Degrees | 10.1016/s0049-237x(08)70024-7 |
| 603–668 | Bibliography, Notation Index, Index | … |

- p. 462 lies in Chapter V "Turing Degrees", which is consistent with a construction of a continuum antichain of Turing degrees.
- The Index ending at p. 668 matches the 1989 edition's xvii+668 pages, so the paging of the 1989 and 1992 printings agrees.

### 3. Theorem number: NOT obtained
- **Blocked:** from MSI, ScienceDirect returned HTML (a bot shell, no PDF) for both `…/pii/S0049237X08700235/pdfft` and the abstract page. The printed page was not seen, so I give no theorem number. A number taken from memory would be a guess.

### 4. Bibliographic data (verified)
- **Vol. I:** zbMATH 0661.03029, P. Odifreddi, *Classical recursion theory. The theory of functions and sets of natural numbers*, Studies in Logic and the Foundations of Mathematics 125, North-Holland, Amsterdam etc. (1989), xvii+668 pp., ISBN 0-444-87295-7.
  - Paperback printing: zbMATH 0744.03044 (1992), ISBN 0-444-89483-7.
  - Volume II is a different book: zbMATH 0931.03057, SLFM 143, Elsevier (1999).
- **The primary source for the antichain, if a primary citation is wanted:**
  - G. E. Sacks, *On suborderings of degrees of recursive unsolvability*, Z. Math. Logik Grundlagen Math. **7** (1961), 46–56. Crossref: Mathematical Logic Quarterly 7(1-5), 46–56, doi 10.1002/malq.19610070109. zbMATH 0118.25202. The Wiley PDF returned HTML from MSI, so its content was NOT read.
  - Also Sacks, *Degrees of Unsolvability*, Ann. of Math. Stud. 55, whose §3 is "Uncountable Suborderings of Degrees", pp. 21–42 (Crossref, De Gruyter reprint doi 10.1515/9781400881840-004). Not read.

### 5. Recommendations for the note
- **Bibitem (FIX, minor):** name the volume and the series, since there are two volumes:
  "P.~Odifreddi, \emph{Classical Recursion Theory}, Vol.~I, Studies in Logic and the Foundations of Mathematics \textbf{125}, North-Holland, Amsterdam, 1989."
- **Locator:** in order of safety:
  - (i) `\cite[Chapter~V]{Odifreddi}`: verified range, Turing degrees;
  - (ii) keep `\cite[p.~462]{Odifreddi}`, knowing it rests on Terwijn's printed citation, consistent with (i);
  - (iii) the lane's fallback, "by a construction of Sacks", citing Sacks 1961 (metadata verified, content not read).
- The statement "the Turing degrees contain an antichain of size continuum" is standard. Terwijn attributes it to Sacks twice. The note's use of it (pairwise non-embeddable groups) is sk-verify-13's review, not mine.
