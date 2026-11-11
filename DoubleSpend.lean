/-!
# nutproof part 3: the mint's double-spend (spent-set) model

The mint stores Y = hash_to_curve(secret) for every redeemed proof (NUT-00/NUT-07).
A swap/melt with inputs `ys` is accepted iff no Y is already spent and the batch has no
duplicate Y; on acceptance all Ys are added atomically. We prove: the spent set only grows,
every accepted Y is recorded, a Y is accepted at most once across ANY sequence of requests,
a rejected request changes nothing, and NUT-07 `checkstate` agrees with the history.
`Y` is abstract (any type with decidable equality); hash_to_curve injectivity is NOT assumed.
-/

namespace NutProof.Spent
variable {Y : Type} [DecidableEq Y]

/-- A request is acceptable iff it is duplicate-free and disjoint from the spent set. -/
def ok (spent ys : List Y) : Bool := ys.Nodup && ys.all (fun y => !(spent.contains y))

/-- Process one request: returns (accepted?, new spent set). Atomic: all or nothing. -/
def step (spent ys : List Y) : Bool × List Y :=
  if ok spent ys then (true, ys ++ spent) else (false, spent)

/-- Rejected requests leave the state untouched. -/
theorem reject_noop (spent ys : List Y) (h : ok spent ys = false) :
    step spent ys = (false, spent) := by simp [step, h]

/-- Monotonicity: spent secrets are never forgotten. -/
theorem spent_mono (spent ys : List Y) (y : Y) (h : y ∈ spent) : y ∈ (step spent ys).2 := by
  unfold step; split <;> simp [h]

/-- Every input of an accepted request is recorded as spent. -/
theorem accepted_recorded (spent ys : List Y) (h : (step spent ys).1 = true) (y : Y)
    (hy : y ∈ ys) : y ∈ (step spent ys).2 := by
  unfold step at *; split at h <;> simp_all

/-- An accepted request contained no already-spent Y. -/
theorem accepted_fresh (spent ys : List Y) (h : (step spent ys).1 = true) (y : Y)
    (hy : y ∈ ys) : y ∉ spent := by
  unfold step at h; split at h
  · rename_i hok
    simp [ok, List.all_eq_true] at hok
    exact hok.2 y hy
  · simp at h

/-- Replay of any already-redeemed proof is rejected. -/
theorem replay_rejected (spent ys : List Y) (y : Y) (hy : y ∈ ys) (hs : y ∈ spent) :
    (step spent ys).1 = false := by
  unfold step; split
  · rename_i hok
    simp [ok, List.all_eq_true] at hok
    exact absurd hs (hok.2 y hy)
  · rfl

/-- Run a sequence of requests; returns the list of accepted requests and the final set. -/
def run : List Y → List (List Y) → List (List Y) × List Y
  | spent, [] => ([], spent)
  | spent, r :: rs =>
    let (a, s') := step spent r
    let (acc, fin) := run s' rs
    (if a then r :: acc else acc, fin)

theorem run_mono (spent : List Y) (rs : List (List Y)) (y : Y) (h : y ∈ spent) :
    y ∈ (run spent rs).2 := by
  induction rs generalizing spent with
  | nil => simpa [run]
  | cons r rs ih => simp only [run]; exact ih _ (spent_mono spent r y h)

/-- Accepted requests are each fresh w.r.t. everything spent before them, and recorded. -/
theorem run_accepted_spent (spent : List Y) (rs : List (List Y)) :
    ∀ r ∈ (run spent rs).1, ∀ y ∈ r, y ∈ (run spent rs).2 := by
  induction rs generalizing spent with
  | nil => simp [run]
  | cons r rs ih =>
    intro r' hr' y hy
    simp only [run] at *
    by_cases ha : (step spent r).1 = true
    · simp [ha] at hr'
      rcases hr' with rfl | hr'
      · exact run_mono _ rs y (accepted_recorded spent r' ha y hy)
      · exact ih _ r' hr' y hy
    · simp [ha] at hr'; exact ih _ r' hr' y hy

/-- Pairwise: no Y appears in two accepted requests, and none was spent initially. -/
def disjointFrom (s : List Y) (acc : List (List Y)) : Prop :=
  ∀ r ∈ acc, ∀ y ∈ r, y ∉ s

theorem run_fresh (spent : List Y) (rs : List (List Y)) :
    disjointFrom spent (run spent rs).1 := by
  induction rs generalizing spent with
  | nil => simp [run, disjointFrom]
  | cons r rs ih =>
    intro r' hr' y hy hsp
    simp only [run] at hr'
    by_cases ha : (step spent r).1 = true
    · simp [ha] at hr'
      rcases hr' with rfl | hr'
      · exact accepted_fresh spent r' ha y hy hsp
      · exact ih _ r' hr' y hy (spent_mono spent r y hsp)
    · simp [ha] at hr'
      have : (step spent r).2 = spent := by unfold step at *; split at ha <;> simp_all
      exact ih (step spent r).2 r' hr' y hy (by rw [this]; exact hsp)

/-- At most once: if a Y is in an accepted request, it is in no LATER accepted request. -/
theorem at_most_once (spent : List Y) (r : List Y) (rs : List (List Y)) (y : Y)
    (ha : (step spent r).1 = true) (hy : y ∈ r) :
    ∀ r' ∈ (run (step spent r).2 rs).1, y ∉ r' := by
  intro r' hr' hy'
  exact run_fresh _ rs r' hr' y hy' (accepted_recorded spent r ha y hy)

/-- NUT-07 checkstate: "SPENT" exactly for Ys in the set. -/
def checkstate (spent : List Y) (y : Y) : String := if spent.contains y then "SPENT" else "UNSPENT"

theorem checkstate_after_accept (spent ys : List Y) (h : (step spent ys).1 = true) (y : Y)
    (hy : y ∈ ys) : checkstate (step spent ys).2 y = "SPENT" := by
  have := accepted_recorded spent ys h y hy
  simp [checkstate, this]

/-- Concrete sanity check: double-spending secret 7 in a second request is refused. -/
example : (run ([] : List Nat) [[7, 8], [9, 7]]).1 = [[7, 8]] := by decide

end NutProof.Spent

#print axioms NutProof.Spent.at_most_once
