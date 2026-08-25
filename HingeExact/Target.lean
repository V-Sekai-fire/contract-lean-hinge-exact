/-
Copyright (c) 2026-present K. S. Ernest (iFire) Lee. All rights reserved.
Released under the MIT license.

# A graph built only from faithful operators computes what the specification says

WHAT THIS MODELS. The accelerator does not sort operators into supported and unsupported. It
sorts them into THREE classes, and the middle one is the dangerous one:

  * accepted and faithful   -- Add, Sub, Mul, Max, Min, Greater. Measured exact.
  * accepted and WRONG      -- Floor, and the f32->s32 Cast. The compiler takes the node and
                               does not perform it. Floor returns its input untouched:
                               measured max |dfc - x| = 0.0 where floor would have moved every
                               element, and max |dfc - floor x| = 0.875.
  * refused                 -- Where, LessOrEqual, GreaterOrEqual, Not, Erf, Sign, Sin, Cos,
                               Ceil, Mod. Parsing fails and nothing runs.

A refusal is loud and costs a day. The middle class is silent and costs a wrong number, which is
why the emitter refuses Floor and Cast at emission rather than passing them along.

WHY THIS IS WORTH PROVING RATHER THAN LISTING. Every decomposition in the emitter -- Where as
`b + p * (a - b)`, logical_and as a mask and a multiply, less_equal as `1 - Greater` -- rests on
one claim: *if every operator in the rewritten graph is accepted and faithful, the graph computes
the function it was rewritten from*. That claim is what `faithful_agrees` states, over an
arbitrary DAG rather than over the handful that have been run.

FIXED POINT, NOT REALS. Values are integers on a scale, so `floor` is `(v / S) * S` and is not
the identity -- over plain integers the defect cannot even be written down. S = 8 matches the
0.125 grid the sweeps used. No Mathlib: every proof here is `simp`, `omega`, `decide` and `rfl`.
-/

namespace HingeExact

/-- The fixed-point scale. 8 is the 0.125 grid the measurements were taken on. -/
def S : Int := 8

inductive Op where
  | add | sub | mul | mx | mn | gt      -- accepted, faithful
  | floor | cast                        -- accepted, NOT performed
  | wher | le                           -- refused at parse
  deriving DecidableEq, Repr

/-- A graph. One input, constants, and unary or binary nodes. -/
inductive Dag where
  | inp
  | const (v : Int)
  | un (o : Op) (a : Dag)
  | bin (o : Op) (a b : Dag)
  deriving Repr

/-- What the ONNX specification says each operator means. -/
def specUn : Op → Int → Int
  | .floor, v => v / S * S
  | .cast, v => v / S * S
  | _, v => v

def specBin : Op → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b / S
  | .mx, a, b => max a b
  | .mn, a, b => min a b
  | .gt, a, b => if b < a then S else 0
  | .le, a, b => if a ≤ b then S else 0
  | _, a, _ => a

/-- The specification's meaning of a whole graph. -/
def spec : Dag → Int → Int
  | .inp, x => x
  | .const v, _ => v
  | .un o a, x => specUn o (spec a x)
  | .bin o a b, x => specBin o (spec a x) (spec b x)

/-- Refused at parse. The graph does not run at all. -/
def Refused : Op → Bool
  | .wher | .le => true
  | _ => false

/-- Accepted, and performs what the specification says. `floor` and `cast` are accepted and do
NOT, which is the whole point of separating this from `Refused`. -/
def Faithful : Op → Bool
  | .floor | .cast => false
  | o => !Refused o

/-- What the ACCELERATOR computes. `none` is a parse refusal. An accepted-but-unfaithful
operator returns a value -- the wrong one -- which is exactly why it cannot be detected by
checking for `none`. -/
def target : Dag → Int → Option Int
  | .inp, x => some x
  | .const v, _ => some v
  | .un o a, x =>
      if Refused o then none
      else match target a x with
        | none => none
        | some v => some (if Faithful o then specUn o v else v)
  | .bin o a b, x =>
      if Refused o then none
      else match target a x, target b x with
        | some p, some q => some (if Faithful o then specBin o p q else p)
        | _, _ => none

/-- Every operator appearing in a graph. -/
def ops : Dag → List Op
  | .inp => []
  | .const _ => []
  | .un o a => o :: ops a
  | .bin o a b => o :: (ops a ++ ops b)

/-- **The theorem the decompositions rest on.** If every operator in a graph is accepted and
faithful, the accelerator computes the specification's function -- for every input, over an
arbitrary graph, not merely the ones that have been run. -/
theorem faithful_agrees (g : Dag) (x : Int) (h : ∀ o ∈ ops g, Faithful o = true) :
    target g x = some (spec g x) := by
  induction g with
  | inp => rfl
  | const v => rfl
  | un o a ih =>
      have ho : Faithful o = true := h o (by simp [ops])
      have hr : Refused o = false := by
        cases o <;> simp_all [Faithful, Refused]
      have ha : ∀ p ∈ ops a, Faithful p = true := fun p hp => h p (by simp [ops, hp])
      simp [target, spec, hr, ho, ih ha]
  | bin o a b iha ihb =>
      have ho : Faithful o = true := h o (by simp [ops])
      have hr : Refused o = false := by
        cases o <;> simp_all [Faithful, Refused]
      have ha : ∀ p ∈ ops a, Faithful p = true := fun p hp => h p (by simp [ops, hp])
      have hb : ∀ p ∈ ops b, Faithful p = true := fun p hp => h p (by simp [ops, hp])
      simp [target, spec, hr, ho, iha ha, ihb hb]

end HingeExact

/-! ## The sweep

Not a claim about the graphs -- the actual values, checked one at a time by the kernel.

The grid is the one the measurements used: x from 0.5 to 5.375 in steps of 0.125, which at
S = 8 is the integers 4 to 43. `native_decide` is deliberately not used; it discharges a goal by
running compiled code, so the kernel never checks it, and `scripts/check_no_sorry.py` refuses it
for that reason. `decide` here is the kernel evaluating every case.
-/

namespace HingeExact

/-- The grid the sweeps were run on: 0.5 .. 5.375 step 0.125, as fixed point at S = 8. -/
def grid : List Int :=
  [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
   24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]

/-- `floor`, standing alone. -/
def floorDag : Dag := .un .floor .inp

/-- `(x + 1) * 0.5`, the case the residual tables use, in accepted faithful operators only. -/
def addMulDag : Dag := .bin .mul (.bin .add .inp (.const 8)) (.const 4)

/-- `max(x, 1)` then `min(..., 4)` -- the clamp shape the mask decompositions use. -/
def clampDag : Dag := .bin .mn (.bin .mx .inp (.const 8)) (.const 32)

/-- SWEPT: on every value of the grid, the accelerator's `floor` disagrees with the
specification. Not "is refused" -- it returns a number, and the number is wrong. -/
theorem floor_wrong_everywhere_off_grid :
    ∀ v ∈ grid, v % S ≠ 0 → target floorDag v ≠ some (spec floorDag v) := by
  decide

/-- SWEPT: and where the value is already on a whole unit, it agrees -- which is precisely why
sampling can miss this. A test that happened to use whole numbers would have found nothing. -/
theorem floor_looks_fine_on_whole_units :
    ∀ v ∈ grid, v % S = 0 → target floorDag v = some (spec floorDag v) := by
  decide

/-- SWEPT: a graph of accepted faithful operators agrees on every value of the grid. This is
`faithful_agrees` for one concrete graph, checked rather than derived. -/
theorem addMul_agrees_on_grid : ∀ v ∈ grid, target addMulDag v = some (spec addMulDag v) := by
  decide

/-- SWEPT: so does the clamp shape. -/
theorem clamp_agrees_on_grid : ∀ v ∈ grid, target clampDag v = some (spec clampDag v) := by
  decide

/-- And the same conclusion from the theorem instead of the sweep, for the same graph -- the two
routes agree, which is the point of having both. -/
theorem addMul_agrees_by_theorem (x : Int) : target addMulDag x = some (spec addMulDag x) :=
  faithful_agrees addMulDag x (by decide)

/-- A refused operator returns nothing at all, on every value. The contrast with
`floor_wrong_everywhere_off_grid` is the whole model: one class is loud, the other is silent. -/
theorem where_refused_everywhere : ∀ v ∈ grid, target (.un .wher .inp) v = none := by
  decide

end HingeExact

/-! ## Lookup tables: which values work, and which do not

The sweeps above answer yes or no. These name the values, because *which* ones fail is the part
that explains why sampling missed the defect for so long.
-/

namespace HingeExact

/-- Does the accelerator agree with the specification at this value? -/
def agreesAt (g : Dag) (v : Int) : Bool := target g v == some (spec g v)

/-- The values of the grid where a graph is computed correctly. -/
def worksOn (g : Dag) : List Int := grid.filter (agreesAt g)

/-- The values where it is not. For `floor` this is not empty and the graph still returns a
number at every one of them. -/
def failsOn (g : Dag) : List Int := grid.filter (fun v => !agreesAt g v)

/-- **The floor table.** It works on exactly the whole units -- 1.0, 2.0, 3.0, 4.0, 5.0 at
S = 8 -- and nowhere else. Five values out of forty.

This is the shape of the trap. `floor` is the identity, so it agrees precisely where the input
was already an integer number of units. A test written with whole numbers finds nothing; the
measurement that caught it used a 0.125 grid. -/
theorem floor_works_only_on_whole_units : worksOn floorDag = [8, 16, 24, 32, 40] := by decide

/-- And it fails on the other thirty-five, returning a number at each. -/
theorem floor_fails_on_thirty_five : (failsOn floorDag).length = 35 := by decide

/-- The two tables partition the grid: nothing is unaccounted for. -/
theorem floor_tables_cover_grid :
    (worksOn floorDag).length + (failsOn floorDag).length = grid.length := by decide

/-- **A faithful graph has an empty failure table.** Not "we tested some values" -- the failure
list is literally `[]` over the whole grid. -/
theorem addMul_never_fails : failsOn addMulDag = [] := by decide

theorem addMul_works_everywhere : worksOn addMulDag = grid := by decide

/-- Same for the clamp shape the mask decompositions are built from. -/
theorem clamp_never_fails : failsOn clampDag = [] := by decide

/-- A REFUSED operator has BOTH tables empty, which is the signature that separates the two
failure modes. `floor` fails on thirty-five values and returns numbers; `where` returns nothing
anywhere, so it never even reaches disagreement. -/
theorem where_works_nowhere_and_fails_everywhere :
    worksOn (.un .wher .inp) = [] ∧ (failsOn (.un .wher .inp)).length = 40 := by decide

end HingeExact
