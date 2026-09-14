#!/bin/bash -l
#SBATCH -J hrf2-certpbig
#SBATCH -p agsmall
#SBATCH -t 12:00:00
#SBATCH --mem=48G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-hyperbolic-rf-2/logs/certpbig.%j.log
# Lane hl-hyperbolic-rf-2: cert_product.g with a 44g GAP workspace, for groups whose listed quotients
# include large targets (HS, PSU(3,9), ...); then the GAP-independent verify_vtf_cert.py.
# Submit with: NAME='G_0^{16,16,48}' INFILE=cckw334_q.g TARGETFILE=targets334_q.g TAG=g0_16_16_48 \
#              sbatch --export=ALL certp_big.sbatch
cd /scratch.global/sauer354/hl-hyperbolic-rf-2 || exit 1
module load sagemath/10.7
export DOT_SAGE=/scratch.global/sauer354/hl-hyperbolic-rf-2/dotsage
mkdir -p out certs
P=out/certp_${TAG}.prelude.g
printf 'INFILE := "%s";; TARGETFILE := "%s";; NAME := "%s";; CERTFILE := "certs/%s.cert";;\n' "$INFILE" "$TARGETFILE" "$NAME" "$TAG" > "$P"
md5sum cert_product.g verify_vtf_cert.py "$INFILE" "$TARGETFILE"
timeout 11h sage -gap -q -o 44g "$P" cert_product.g < /dev/null > out/certp_${TAG}.out 2>&1
echo EXIT=$? >> out/certp_${TAG}.out
/usr/bin/python3.12 verify_vtf_cert.py certs/${TAG}.cert > out/verify_${TAG}.out 2>&1
echo EXIT=$? >> out/verify_${TAG}.out
md5sum certs/${TAG}.cert
