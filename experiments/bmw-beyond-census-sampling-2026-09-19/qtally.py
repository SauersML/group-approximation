# qtally.py qsphere.jsonl : per degree pattern, how many classes have Q_A, Q_B finite / infinite.
# Q is infinite when its abelian invariants contain 0 (a Z factor); finite when transitive (Step 5) or
# when coset enumeration returned a size.
import sys, json, re, collections
def kind(q):
    if q.startswith('1 (transitive)'): return 'fin'
    inv = re.findall(r'-?\d+', q.split(']')[0]); size = int(q.split(']')[1])
    if '0' in inv: return 'inf'
    return 'fin' if size > 0 else 'unk'
T = collections.defaultdict(collections.Counter); ALL = collections.Counter()
for l in open(sys.argv[1]):
    r = json.loads(l); a, b = kind(r['QA']['Q']), kind(r['QB']['Q'])
    key = 'both finite' if a == b == 'fin' else ('both infinite' if a == b == 'inf' else
          ('one infinite' if 'inf' in (a, b) else 'undecided'))
    T[r['pat']][key] += 1; ALL[key] += 1
    if len(sys.argv) > 2 and r['pat'] == sys.argv[2]: print(r['idx'], a, b, r['QA']['Q'], r['QB']['Q'])
for p in sorted(T): print(p, dict(T[p]))
print('ALL', sum(ALL.values()), dict(ALL))
