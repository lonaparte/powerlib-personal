#!/bin/bash
cd "$(dirname "$0")"
mkdir -p sweep20
{ echo "d5.py gfl"; echo "d5.py gfm"; echo "f5.py gfm";
  echo "f5.py gfl"; echo "e5.py gfm"; echo "e5.py gfl"; } \
  | xargs -P 3 -I{} sh -c 'python {}'
echo "FIVEDONE"
