
discard """
  output: '''occupied ok: true
total ok: true'''
"""

import strutils, data

proc main =
  var m = 0
  for i in 0..1000_000:
    let size = sizes[i mod sizes.len]
    let p = alloc(size)
    if p == nil:
      quit "could not serve request!"
    dealloc p
 #   c_fprintf(stdout, "iteration: %ld size: %ld\n", i, size)

main()

let occ = getOccupiedMem()
let total = getTotalMem()

# Current values on Win64: 824KiB / 106.191MiB

echo "occupied ok: ", occ < 2 * 1024 * 1024
echo "total ok: ", total < 120 * 1024 * 1024
