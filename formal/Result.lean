import Assignment
import Normalization
import Sharpness
import Schedules
import Ties
import Algorithm1

namespace Gasoline.Integer
/-- For every K=r+3, an original-index input attains 2K-2 and has optimum K.
Counts and the actual comparison schedule are part of the statement. -/
theorem exact_ratio_witness (r : ℕ) :
    let h : ℤ := (r:ℤ)+2
    let ds := 1::blocks h 0 r
    ∃ xs a b,
      HeadRun h ds xs 0 0 0 (2*h-1) ∧
      (∀ x ∈ xs, x=0 ∨ x=h) ∧ xs.count h=r+2 ∧ xs.count 0=r+1 ∧
      a≤0 ∧ 0≤b ∧ Schedule h (r+2) (r+1) ds 0 a b ∧ b-a=h ∧
      (∀ a' b', a'≤0 → 0≤b' → Schedule h (r+2) (r+1) ds 0 a' b' → h≤b'-a') := by
  let h : ℤ := (r:ℤ)+2
  let ds := 1::blocks h 0 r
  have hh : 1≤h := by dsimp [h]; omega
  rcases sharp_family r with ⟨hd,hlen,htotal,hval,good,bad⟩
  obtain ⟨xs,hhead,hxs,hbig,hsmall⟩ := run_realizable hh bad
  obtain ⟨a,b,ha,hb,hs,he⟩ := run_has_schedule good (by simpa using htotal)
  refine ⟨xs,a,b,hhead,hxs,hbig,hsmall,ha,hb,hs,he,?_⟩
  intro a' b' ha' hb' schedule
  have H := schedule_lower (by omega : 0≤h) hd ha' hb' schedule
  rw [hval] at H
  exact H

#print axioms Gasoline.assignment_to_fraction
#print axioms Gasoline.fraction_to_assignment
#print axioms Gasoline.normalization
#print axioms Gasoline.reach_iff
#print axioms Gasoline.prefix_lower
#print axioms Gasoline.prefix_attained
#print axioms Gasoline.Integer.score_formula
#print axioms Gasoline.Integer.approximation
#print axioms Gasoline.Integer.compared_to_schedule
#print axioms Gasoline.Integer.ratio_bound
#print axioms Gasoline.Integer.run_realizable
#print axioms Gasoline.Integer.exact_ratio_witness
end Gasoline.Integer

namespace Gasoline.Integer
/-- The matching extremal trace is also a run of the independently defined LP rule. -/
theorem sharp_lp_run (r : ℕ) :
    let h : ℤ := (r:ℤ)+2
    Algorithm1Run h (r+2) (r+1) (1::blocks h 0 r) 0 0 0 (2*h-1) := by
  rcases sharp_family r with ⟨hd,hlen,htotal,_,_,bad⟩
  have valid : ValidPrefix ((r:ℤ)+2) (r+2) (r+1)
      (1::blocks ((r:ℤ)+2) 0 r) 0 0 0 :=
    ⟨hd,hlen,by simpa using htotal,le_rfl,le_rfl,le_rfl,le_rfl⟩
  exact (run_iff_algorithm1 (by omega) valid).mp bad
end Gasoline.Integer

#print axioms Gasoline.assignment_delivery
#print axioms Gasoline.Integer.sharp_lp_run

#print axioms Gasoline.matrixBand_iff_band
#print axioms Gasoline.matrixLP_value
#print axioms Gasoline.Integer.ValidPrefix.lp_value
#print axioms Gasoline.Integer.small_choice_iff
#print axioms Gasoline.Integer.large_choice_iff
#print axioms Gasoline.Integer.run_iff_algorithm1
#print axioms Gasoline.Integer.algorithm1_additive_guarantee
#print axioms Gasoline.Integer.algorithm1_ratio_bound
#print axioms Gasoline.Integer.algorithm1_two_approximation
#print axioms Gasoline.Integer.algorithm1_exists
