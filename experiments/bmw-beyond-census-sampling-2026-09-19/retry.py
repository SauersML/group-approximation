# retry.py in.jsonl k R SHORT MAXL TMO : re-run the cone-tree search on record k of in.jsonl at (R, SHORT),
# check the tree independently (check_tree) and print a one-line JSON summary; tree saved to trees/.
import sys, json, os
from sample import VH, ctree, check_tree, cinput
from vh_enum import inv_arr
recs = [json.loads(l) for l in open(sys.argv[1])]; r = recs[int(sys.argv[2])]
R, sh, maxl, tmo = map(int, sys.argv[3:7])
m, pA, n, pB = int(r['pat'][0]), int(r['pat'][1]), int(r['pat'][3]), int(r['pat'][4])
SQ = {tuple(a): tuple(b) for a, b in r['sq']}
G = VH(inv_arr(m, pA), inv_arr(n, pB), SQ); G.confluence()
c, o, e = ctree(G, R, sh, maxl, tmo)
out = dict(pat=r['pat'], seed=r['seed'], k=r['k'], R=R, short=sh, code=c, err=e.strip().split('\n')[-1][:200])
if c == 0:
    t = json.loads(o); out.update(depth=t['depth'], leaves=t['leaves'], ok=check_tree(G, t['tree']))
    os.makedirs('trees', exist_ok=True)
    json.dump(t, open('trees/%s_s%d_k%d_R%ds%d.json' % (r['pat'], r['seed'], r['k'], R, sh), 'w'))
else: out['msg'] = o.strip()[:200]
print(json.dumps(out)); sys.stdout.flush()
