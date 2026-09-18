cd /scratch.global/sauer354/bh-groupoid && mkdir -p arxq && cd arxq
q() { curl -s -A 'Mozilla/5.0' "http://export.arxiv.org/api/query?search_query=$1&start=0&max_results=60&sortBy=submittedDate&sortOrder=descending" -o "$2.xml"; sleep 3; }
q 'all:%22Boone-Higman%22' bh
q 'abs:%22finitely%20presented%20simple%22%20AND%20abs:building' fpsb
q 'abs:%22finitely%20presented%20simple%22%20AND%20abs:lattice' fpsl
q 'abs:%22Robertson-Steger%22' rs
q 'abs:%22topological%20full%20group%22%20AND%20abs:%22higher%20rank%20graph%22' tfgk
q 'abs:%22tilde%20A_2%22%20AND%20abs:simple' a2s
q 'abs:%22triangle%20building%22' tri
for f in *.xml; do echo "=== $f"; python3 - "$f" <<'PY'
import sys,re
t=open(sys.argv[1]).read()
for e in re.findall(r'<entry>(.*?)</entry>',t,re.S):
    title=re.sub(r'\s+',' ',re.search(r'<title>(.*?)</title>',e,re.S).group(1))
    pub=re.search(r'<published>(.*?)</published>',e).group(1)[:10]
    idd=re.search(r'<id>(.*?)</id>',e).group(1).split('/abs/')[-1]
    if pub>='2023': print(pub,idd,title[:150])
PY
done
