-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

import Lake
open Lake DSL

package «lean-hinge-exact» where

-- NO MATHLIB, AND THAT IS THE POINT OF THE SPLIT. `lean-deform-exact` needs it: `Tent.lean` is
-- stated over ℝ with `|·|` and `Finset`. Nothing here is. The hinge sum is proved over `Int`,
-- which is both Mathlib-free and the closer model -- the accelerator this targets does integer
-- arithmetic, so a proof over ℤ describes what actually runs rather than an idealisation of it.
--
-- The cost of the dependency is the reason to avoid it: Mathlib is a multi-gigabyte fetch and a
-- long build for a file whose every tactic is `simp`, `omega`, `congr` and `rw`.
@[default_target]
lean_lib «HingeExact» where
  roots := #[`HingeExact]
