set -u
W=/projects/standard/hsiehph/sauer354/cc-gk-steward; cd "$W" || exit 1
echo "clone HEAD=$(git rev-parse --short HEAD) graph mtime=$(date -r .cairn/cache/graph.json +%H:%M 2>/dev/null)"
nice -n 10 /usr/bin/python3.11 - "$@" <<'EOF'
import json, sys
g = json.load(open('.cairn/cache/graph.json'))['nodes']
reg = set(open('/projects/standard/hsiehph/sauer354/gk-steward/region-ids.txt').read().split())
for i in sys.argv[1:]:
    n = g.get(i)
    print('STATUS', n['status'] if n else 'NOT-IN-GRAPH', 'reach' if n and n.get('reachable') else 'unreach', i)
for i in sorted(reg):
    if i in g and ('gamma' in i or 'el3j' in i):
        print('MATCH', g[i]['kind'], g[i]['status'], i)
EOF
echo STATQ-DONE
