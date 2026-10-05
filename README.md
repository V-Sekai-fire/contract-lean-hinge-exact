# contract-lean-hinge-exact

A Lean 4 proof, over the integers and without Mathlib, that a hinge-sum piecewise linear approximation has slope exactly `s m` on segment `m`.

## What it is for

Some accelerator compilers refuse the error function but accept subtract, max, multiply and add, which is enough to write a piecewise linear approximation as a sum of hinges. The multiplier on each hinge is the change in slope rather than the slope, and the wrong pairing still looks plausible at sampled points, so the property is proved for an arbitrary knot sequence. The proof is over the integers because the accelerator computes in integers.

## Build and run

```sh
lake build
python scripts/check_no_sorry.py .
```

The build succeeds even with open goals, so the script is the check that every proof is closed.

## Licence

MIT; see LICENSE.
