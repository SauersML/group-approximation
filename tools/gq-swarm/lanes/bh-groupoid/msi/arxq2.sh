cd /scratch.global/sauer354/bh-groupoid/arxq
q() { curl -s -A 'Mozilla/5.0' "https://export.arxiv.org/api/query?search_query=$1&start=0&max_results=80&sortBy=submittedDate&sortOrder=descending" -o "$2.xml"; sleep 3; }
q 'abs:building%20AND%20abs:%22simple%20group%22%20AND%20abs:%22finitely%20presented%22' b2
q 'abs:%22affine%20building%22%20AND%20abs:%22full%20group%22' b3
q 'abs:exotic%20AND%20abs:building%20AND%20abs:lattice' b4
q 'abs:%22triangle%20presentation%22' b5
q 'abs:%22higher%20rank%20graph%22%20AND%20abs:%22finitely%20presented%22' b6
q 'abs:%22Boone%22%20AND%20abs:%22Higman%22' b7
q 'abs:%22simple%20envelope%22' b8
for f in b2 b3 b4 b5 b6 b7 b8; do echo "=== $f"; python3 - "$f.xml" <<'PY'
import sys,re
t=open(sys.argv[1]).read()
for e in re.findall(r'<entry>(.*?)</entry>',t,re.S):
    title=re.sub(r'\s+',' ',re.search(r'<title>(.*?)</title>',e,re.S).group(1))
    pub=re.search(r'<published>(.*?)</published>',e).group(1)[:10]
    idd=re.search(r'<id>(.*?)</id>',e).group(1).split('/abs/')[-1]
    s=re.sub(r'\s+',' ',re.search(r'<summary>(.*?)</summary>',e,re.S).group(1))
    flag='*' if re.search(r'building|A_2|\\tilde|lattice',s) else ' '
    if pub>='2023': print(flag,pub,idd,title[:120])
PY
done
echo "=== abstracts of BH hits mentioning buildings"
python3 - <<'PY'
import re
t=open('bh.xml').read()+open('b7.xml').read()
for e in re.findall(r'<entry>(.*?)</entry>',t,re.S):
    s=re.sub(r'\s+',' ',re.search(r'<summary>(.*?)</summary>',e,re.S).group(1))
    idd=re.search(r'<id>(.*?)</id>',e).group(1).split('/abs/')[-1]
    if re.search(r'building|lattice|CAT\(0\)|A_2',s): print(idd,':',s[:700]); print()
PY
