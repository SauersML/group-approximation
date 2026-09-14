#!/bin/bash -l
#SBATCH -J hrf2-cert
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=12G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-hyperbolic-rf-2/logs/cert.%j.log
# Lane hl-hyperbolic-rf-2: export a vertex-injective quotient certificate with cert_vtf.g and check it with
# the GAP-independent verify_vtf_cert.py.
# Submit with: sbatch --export=ALL,INFILE=cckw334_q.g,NAME='G_4^{14,14,48}',BOUND=5040,TAG=g4_14_14_48 cert.sbatch
cd /scratch.global/sauer354/hl-hyperbolic-rf-2 || exit 1
module load sagemath/10.7
export DOT_SAGE=/scratch.global/sauer354/hl-hyperbolic-rf-2/dotsage
mkdir -p out certs
P=out/cert_${TAG}.prelude.g
printf 'INFILE := "%s";; NAME := "%s";; INDEXBOUND := %d;; CERTFILE := "certs/%s.cert";;\n' "$INFILE" "$NAME" "$BOUND" "$TAG" > "$P"
md5sum cert_vtf.g verify_vtf_cert.py "$INFILE"
timeout 3h sage -gap -q -o 10g -l ";/scratch.global/sauer354/hl-hyperbolic-rf-2/gaproot" "$P" cert_vtf.g < /dev/null > out/cert_${TAG}.out 2>&1
echo EXIT=$? >> out/cert_${TAG}.out
/usr/bin/python3.12 verify_vtf_cert.py certs/${TAG}.cert > out/verify_${TAG}.out 2>&1
echo EXIT=$? >> out/verify_${TAG}.out
md5sum certs/${TAG}.cert
