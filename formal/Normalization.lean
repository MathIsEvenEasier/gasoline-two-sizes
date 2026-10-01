import Reachability

namespace Gasoline
/-- Original units: a delivery lies between 1 and K; demand is consumed after
its delivery, so both types of event are explicitly constrained. -/
def OriginalReach (K : ℝ) : List ℝ → ℝ → ℝ → ℝ → Prop
  | [], s, _, _ => s=0
  | y::ys, s, a, b => ∃ q : ℝ, 1 ≤ q ∧ q ≤ K ∧ s+q ≤ b ∧
      a ≤ s+q-y ∧ OriginalReach K ys (s+q-y) a b

theorem normalization (h : ℝ) (ds : List ℝ) (s a b : ℝ) :
    OriginalReach (h+1) (ds.map (fun d => d+1)) s a (b+1) ↔ Reach h ds s a b := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons,OriginalReach,Reach]
    constructor
    · rintro ⟨q,hq1,hqK,hpeak,htrough,htail⟩
      refine ⟨q-1,by linarith,by linarith,by linarith,by linarith,?_⟩
      have eq : s+(q-1)-d=s+q-(d+1) := by ring
      rw [eq]
      exact (ih _).mp htail
    · rintro ⟨z,hz0,hzh,hpeak,htrough,htail⟩
      refine ⟨z+1,by linarith,by linarith,by linarith,by linarith,?_⟩
      have eq : s+(z+1)-(d+1)=s+z-d := by ring
      rw [eq]
      exact (ih _).mpr htail

#print axioms Gasoline.normalization
end Gasoline
