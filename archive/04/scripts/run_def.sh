#!/bin/bash
cd "$(dirname "$0")"
mkdir -p sweep20
{ echo "gflcases.py D"; echo "gfmcases.py D"; echo "gfmcases.py F";
  echo "gflcases.py F"; echo "gfmcases.py E"; echo "gflcases.py E"; } \
  | xargs -P 3 -I{} sh -c 'python {}'
echo "ALLDONE"
