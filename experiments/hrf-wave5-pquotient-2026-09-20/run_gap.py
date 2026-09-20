"""Bounded GAP runner retaining stdout, stderr, timeout, and exit status."""
from pathlib import Path
import argparse,subprocess,json,time

ap=argparse.ArgumentParser();ap.add_argument('--class-bound',type=int,default=9)
ap.add_argument('--seconds',type=int,default=90);ap.add_argument('--save',type=Path)
ap.add_argument('--restore',type=Path)
ap.add_argument('--stage',choices=('all','prepare','lift','finish'),default='all')
ap.add_argument('--label',default='',help='Distinct suffix for checkpoint-batch logs.')
args=ap.parse_args();base=Path(__file__).resolve().parent
if args.restore and not args.save:ap.error('restored steps require an explicit --save path')
result=base/f'class{args.class_bound}.json'
stem=f'class{args.class_bound}'+('' if args.stage=='all' else '-'+args.stage)
if args.label:stem+='-'+args.label
log=base/f'{stem}.log'
code='if IsBound(HRF_SAVE) then Unbind(HRF_SAVE);fi;'
code+=f'HRF_CLASS:={args.class_bound};HRF_STAGE:="{args.stage}";HRF_RESULT:="{result}";'
if args.save:code+=f'HRF_SAVE:="{args.save}";'
source='advance.g' if args.restore else 'pquotient.g'
code+=f'Read("{base / source}");'
command=['/tmp/gap-4.15.1/gap','--bare','-q']
if args.restore:command+=['-L',str(args.restore)]
command+=['-c',code]
started=time.monotonic()
try:
    run=subprocess.run(command,
                       capture_output=True,text=True,timeout=args.seconds)
    log.write_text(run.stdout+run.stderr)
    receipt={'return_code':run.returncode,'timed_out':False,'seconds':time.monotonic()-started}
except subprocess.TimeoutExpired as exc:
    def decode(s):return s.decode() if isinstance(s,bytes) else (s or '')
    log.write_text(decode(exc.stdout)+decode(exc.stderr))
    receipt={'return_code':None,'timed_out':True,'seconds':time.monotonic()-started}
(base/f'{stem}-run.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(log.read_text());print(json.dumps(receipt,indent=2))
