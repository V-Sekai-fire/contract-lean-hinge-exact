/-- One hinge: `max (x - c) 0` -- a `Sub` and a `Max`, which is all the accelerator needs. -/
def hinge (c x : Int) : Int := max (x - c) 0

theorem hinge_of_le {c x : Int} (h : x ≤ c) : hinge c x = 0 := by
  simp [hinge]; omega

theorem hinge_of_ge {c x : Int} (h : c ≤ x) : hinge c x = x - c := by
  simp [hinge]; omega

/-- The coefficients the emitter must use: the slope CHANGE at each interior knot. -/
def coeffs (s : Nat → Int) : Nat → List Int
  | 0 => []
  | m + 1 => coeffs s m ++ [s (m + 1) - s m]

/-- **The telescoping.** This is the identity a misaligned index breaks, and the reason the
coefficient is `s k - s (k-1)` rather than `s k`. -/
theorem coeffs_sum (s : Nat → Int) : ∀ m, (coeffs s m).sum = s m - s 0
  | 0 => by simp [coeffs]
  | m + 1 => by
    simp [coeffs, List.sum_append, coeffs_sum s m]
    omega

/-- A knot list is ACTIVE below `x` when every knot is at or below it. -/
def AllLe (ts : List Int) (x : Int) : Prop := ∀ t ∈ ts, t ≤ x

/-- Every active hinge contributes its coefficient times the run. -/
theorem sum_active (x y : Int) (hxy : x ≤ y) :
    ∀ (tcs : List (Int × Int)), AllLe (tcs.map Prod.fst) x →
      ((tcs.map (fun p => p.2 * hinge p.1 y)).sum
        - (tcs.map (fun p => p.2 * hinge p.1 x)).sum)
      = (tcs.map Prod.snd).sum * (y - x)
  | [], _ => by simp
  | (t, c) :: rest, h => by
    have ht : t ≤ x := h t (by simp)
    have hrest : AllLe (rest.map Prod.fst) x := by
      intro u hu; exact h u (by simp [hu])
    have ih := sum_active x y hxy rest hrest
    have key : c * (y - t) - c * (x - t) = c * (y - x) := by
      rw [← Int.mul_sub]; congr 1; omega
    simp only [List.map_cons, List.sum_cons, hinge_of_ge ht, hinge_of_ge (Int.le_trans ht hxy)]
    rw [Int.add_mul, ← ih, ← key]
    omega

/-- Every inactive hinge contributes nothing. -/
theorem sum_inactive (x y : Int) (hxy : x ≤ y) :
    ∀ (tcs : List (Int × Int)), (∀ t ∈ tcs.map Prod.fst, y ≤ t) →
      (tcs.map (fun p => p.2 * hinge p.1 y)).sum
        = (tcs.map (fun p => p.2 * hinge p.1 x)).sum
  | [], _ => by simp
  | (t, c) :: rest, h => by
    have ht : y ≤ t := h t (by simp)
    have hrest : ∀ u ∈ rest.map Prod.fst, y ≤ u := by
      intro u hu; exact h u (by simp [hu])
    have ih := sum_inactive x y hxy rest hrest
    simp only [List.map_cons, List.sum_cons, hinge_of_le ht, hinge_of_le (Int.le_trans hxy ht),
      Int.mul_zero]
    omega

/-- **The theorem.** Split the knots into those at or below `x` and those at or above `y`;
between those two points the hinge sum rises by the ACTIVE coefficients times the run, and by
nothing else.

Combined with `coeffs_sum`, this is what forces the emitter's coefficient. If the active
coefficients are `s 1 - s 0, ..., s m - s (m-1)` they telescope to `s m - s 0`, and adding the
base slope `s 0` gives slope exactly `s m` on segment `m`. Pair them any other way and the sum
does not collapse, which is the bug this file exists to make unstateable. -/
theorem hingeSum_increment (x y : Int) (hxy : x ≤ y) (act inact : List (Int × Int))
    (ha : AllLe (act.map Prod.fst) x) (hi : ∀ t ∈ inact.map Prod.fst, y ≤ t) :
    (((act ++ inact).map (fun p => p.2 * hinge p.1 y)).sum
      - ((act ++ inact).map (fun p => p.2 * hinge p.1 x)).sum)
      = (act.map Prod.snd).sum * (y - x) := by
  simp only [List.map_append, List.sum_append]
  have hact := sum_active x y hxy act ha
  have hin := sum_inactive x y hxy inact hi
  omega
