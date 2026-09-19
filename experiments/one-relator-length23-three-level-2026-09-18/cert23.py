"""Census certificates (census.cert_word: PEEL, PP, R1, CYC, PRIMITIVE, depth 8) for the
length-23 candidates.  Input: a gen_walk21.py .seq file (lines 'SEQ [...]') or a previous
.cert file (the syllable list is the 4th field).  The search budget (4000 cert_word calls)
is reset for EACH relator, so a relator is OPEN only when its own search fails.
Output: CERT|OPEN word length seq reason."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, '../../research/artifacts/or-unpeelable-census-scripts-2026-09-12')))
import census as C
from ast import literal_eval
for line in open(sys.argv[1]):
    if line.startswith('SEQ '):
        seq = literal_eval(line[4:])
    elif line.startswith(('CERT ', 'OPEN ')):
        seq = literal_eval(line.split()[3])
    else:
        continue
    w = C.cyc_reduce(C.seq_to_word(seq))
    C.BUDGET[0] = 4000
    r = C.cert_word(w, 0)
    print('CERT' if r[0] else 'OPEN', C.word_str(w), len(w), repr(seq).replace(' ', ''), r[1], flush=True)
