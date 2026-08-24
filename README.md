# lean-hinge-exact

A piecewise linear approximation, emitted as a sum of hinges, has slope exactly `s m` on
segment `m` — proved over `Int`, with no Mathlib.

## Why this exists

The Hailo Dataflow Compiler refuses `Erf` standing alone, and refuses it again in the `Mul, Erf`
form its own documentation calls Gelu. It accepts `Sub`, `Max`, `Mul` and `Add`. That is exactly
enough to write a piecewise linear approximation as a hinge sum:

    f x ≈ f t₀ + s₀ * (x - t₀) + ∑ k, (s k - s (k-1)) * max (x - t k) 0

which is the shape an NPU implements in hardware as a knot table, written here as ordinary
tensor arithmetic. Hinge terms were measured compiling for `hailo10h` at small counts.

## What the coefficient cost

The multiplier on the `k`-th hinge is the slope **change**, `s k - s (k-1)`, not the slope.
Written with the wrong pairing the result still looks right: continuous, close to the target, and
its error shrinks as the domain narrows — so every cheap check passes.

Two separate constructions were measured against a reference and written up as compiler defects
before the arithmetic was recomputed with nothing compiled and found to be at fault. The first
was out by 1.284628. The second, after a correction, still fitted **worse** at four segments than
at three, which cannot happen for a correct interpolant.

So the property is stated over an arbitrary knot sequence rather than checked at samples. A
misaligned index cannot satisfy `coeffs_sum`, because the telescoping is what collapses the
partial sum to `s m`.

## Why no Mathlib

`lean-deform-exact` needs it — `Tent.lean` is stated over ℝ with `|·|` and `Finset`. Nothing here
is. The hinge sum is proved over `Int`, which is Mathlib-free and also the closer model: the
accelerator does integer arithmetic, so a proof over ℤ describes what runs rather than an
idealisation of it.

Measured: `lake build` completes in about one second. Mathlib is a multi-gigabyte fetch and a
long build, for a file whose every tactic is `simp`, `omega`, `congr` and `rw`.

## The theorems

| name | says |
| --- | --- |
| `hinge_of_le` | below its knot a hinge is flat |
| `hinge_of_ge` | at or above its knot it is the identity, shifted |
| `coeffs_sum` | `∑ (s (k+1) - s k) = s m - s 0` — the telescoping |
| `sum_active` | knots at or below `x` contribute coefficient × run |
| `sum_inactive` | knots at or above `y` contribute nothing |
| `hingeSum_increment` | between two points in a segment, the rise is the active coefficients times the run, and nothing else |

## Checking

    lake build
    python scripts/check_no_sorry.py .

`sorry` typechecks, so the build is not the gate — `lake build` exits 0 whether every goal is
closed or none are. The script scans with comments stripped, and refuses `sorryAx` and
`native_decide` as well.
