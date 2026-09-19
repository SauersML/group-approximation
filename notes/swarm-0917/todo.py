import json,os,sys,subprocess
J,H=sys.argv[1],sys.argv[2]
R='/home/user/group-approximation'
def git(*a): return subprocess.run(['git','-C',R,*a],capture_output=True,text=True)
st={};work={};land={}
for l in open(J):
  d=json.loads(l)
  if d.get('type')=='started': st[d.get('agentId')]=d.get('label')
  elif d.get('type')=='result' and isinstance(d.get('result'),dict):
    lab=st.get(d.get('agentId'),'?'); k=lab.split(':',1)[1]
    (work if lab.startswith('work:') else land)[k]=d['result']
held=set(l.split('\t')[0] for l in open(H)) if os.path.exists(H) else set()
print('work',len(work),'land',len(land),'held',len(held),file=sys.stderr)
for k,r in land.items():
  w=work.get(k,{})
  wt=w.get('worktree')
  if not wt or not os.path.isdir(wt): continue
  key=k
  if k in held:
    # a lane re-run after resume: emit only if its worktree has commits not yet held
    h=subprocess.run(['git','-C',wt,'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()
    if not h: continue
    if git('merge-base','--is-ancestor',h,'HEAD').returncode==0: continue
    if git('merge-base','--is-ancestor',h,'refs/swarm-hold/'+k).returncode==0: continue
    key=k+'-r'+h[:7]
    if key in held: continue
  print(key, w.get('id'), int(bool(r.get('landed'))), wt, sep='\t')
