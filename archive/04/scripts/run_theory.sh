#!/bin/bash
cd "$(dirname "$0")"
mkdir -p sweep20
{ echo "dtheory.py gfl"; echo "dtheory.py gfm"; echo "rates.py gfl";
  echo "rates.py gfm"; echo "emtheory.py"; echo "etheory.py"; } \
  | xargs -P 3 -I{} sh -c 'python {}'
echo "THEORYDONE"
