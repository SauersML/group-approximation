# Pack the cone-tree certificates trees/tree_<pat>_<cls>.json (dtree2.py output) into one gzipped
# JSON-lines file, one record {"pat", "cls", "R", "depth", "leaves", "tree"} per class.
# usage: pack_trees.py trees_dir out.jsonl.gz
import sys, json, gzip, glob, os
recs = []
for f in glob.glob(os.path.join(sys.argv[1], 'tree_*.json')):
    b = os.path.basename(f)[5:-5]; pat, cls = b.rsplit('_', 1)
    t = None
    for line in open(f):
        if line.startswith('{'): t = json.loads(line)
    assert t and t['cls'] == int(cls), f
    recs.append(dict(pat=pat, cls=int(cls), R=t['R'], depth=t.get('depth'), leaves=t['leaves'], tree=t['tree']))
recs.sort(key=lambda r: (r['pat'], r['cls']))
with gzip.open(sys.argv[2], 'wt') as g:
    for r in recs: g.write(json.dumps(r, separators=(',', ':')) + '\n')
print(len(recs), 'trees packed')
