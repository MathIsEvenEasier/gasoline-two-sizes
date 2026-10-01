import IntegerModel

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000

namespace Gasoline.Integer

/-- Position-first iterative rounding, allowing every exact tie choice.
Counts record available supplies; the returned integer is the actual trace range. -/
inductive Run (h : ℤ) : ℕ → ℕ → List ℤ → ℤ → ℤ → ℤ → ℤ → Prop
  | done (s A B : ℤ) : Run h 0 0 [] s A B (B-A)
  | small {m k : ℕ} {d s A B C : ℤ} {ds : List ℤ}
      (choose : m=0 ∨ score h d ds s A B 0 ≤ score h d ds s A B h)
      (tail : Run h m k ds (s-d) (min A (s-d)) (max B s) C) :
      Run h m (k+1) (d::ds) s A B C
  | large {m k : ℕ} {d s A B C : ℤ} {ds : List ℤ}
      (choose : k=0 ∨ score h d ds s A B h ≤ score h d ds s A B 0)
      (tail : Run h m k ds (s+h-d) (min A (s+h-d)) (max B (s+h)) C) :
      Run h (m+1) k (d::ds) s A B C

/-- Invariant for every intermediate prefix of every legal run. -/
theorem run_bound {h : ℤ} (hh : 1 ≤ h) {m k : ℕ} {ds : List ℤ} {s A B C : ℤ}
    (run : Run h m k ds s A B C) (L0 : ℤ)
    (hd : ∀ d ∈ ds, 0 ≤ d) (hlen : ds.length=m+k)
    (htotal : ds.sum-s=h*m)
    (hA : A ≤ 0) (hB : 0 ≤ B) (hAs : A ≤ s) (hsB : s ≤ B)
    (hV : internal h ds ≤ L0) (hL : value h ds s A B ≤ L0+h-1) : C ≤ L0+h-1 := by
  induction run with
  | done s A B =>
    simp only [List.sum_nil, Nat.cast_zero, mul_zero] at htotal
    simp only [value,internal,terminal,deficit] at hL
    omega
  | @small m k d s A B C ds choose tail ih =>
    have hd0 : 0 ≤ d := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e := by intro e he; exact hd e (by simp [he])
    have hlen' : ds.length=m+k := by simp only [List.length_cons] at hlen; omega
    have htotal' : ds.sum-(s-d)=h*m := by simp only [List.sum_cons] at htotal; omega
    have hv' : internal h ds ≤ L0 := le_trans (le_max_left _ _) hV
    have hscore : score h d ds s A B 0 ≤ L0+h-1 := by
      by_cases hm : m=0
      · have he0 : (d::ds).sum-s=0 := by simp [hm] at htotal; exact htotal
        have H := forced_score h d ds s A B 0 (by omega) hd0 hds hA hB hAs hsB
          (by omega) (by rw [he0,budget_length]; positivity) (Or.inl ⟨rfl,he0⟩)
        omega
      · have ch : score h d ds s A B 0 ≤ score h d ds s A B h := choose.resolve_left hm
        have H := both_choices_bound h d L0 ds s A B hh hAs hsB hL hV
        omega
    apply ih hds hlen' htotal'
      (le_trans (min_le_left _ _) hA) (le_trans hB (le_max_left _ _))
      (min_le_right _ _) (by have := le_max_right B s; omega) hv'
    simpa [score] using hscore
  | @large m k d s A B C ds choose tail ih =>
    have hd0 : 0 ≤ d := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e := by intro e he; exact hd e (by simp [he])
    have hlen' : ds.length=m+k := by simp only [List.length_cons] at hlen; omega
    have htotal' : ds.sum-(s+h-d)=h*m := by
      simp only [List.sum_cons,Nat.cast_add,Nat.cast_one,mul_add,mul_one] at htotal
      omega
    have hv' : internal h ds ≤ L0 := le_trans (le_max_left _ _) hV
    have hscore : score h d ds s A B h ≤ L0+h-1 := by
      by_cases hk : k=0
      · have heN : (d::ds).sum-s=budget h (d::ds) := by
          rw [budget_length,hlen,hk,Nat.add_zero]
          exact htotal
        have H := forced_score h d ds s A B h (by omega) hd0 hds hA hB hAs hsB
          (by rw [heN,budget_length]; positivity) (by omega) (Or.inr ⟨rfl,heN⟩)
        omega
      · have ch : score h d ds s A B h ≤ score h d ds s A B 0 := choose.resolve_left hk
        have H := both_choices_bound h d L0 ds s A B hh hAs hsB hL hV
        omega
    apply ih hds hlen' htotal'
      (le_trans (min_le_left _ _) hA) (le_trans hB (le_max_left _ _))
      (min_le_right _ _) (by have := le_max_right B (s+h); omega) hv'
    exact hscore

/-- Universal normalized guarantee, with no restriction on tie choices. -/
theorem approximation {h : ℤ} (hh : 1 ≤ h) {m k : ℕ} {ds : List ℤ} {C : ℤ}
    (hd : ∀ d ∈ ds, 0 ≤ d) (hlen : ds.length=m+k) (htotal : ds.sum=h*m)
    (run : Run h m k ds 0 0 0 C) : C ≤ value h ds 0 0 0+h-1 := by
  apply run_bound hh run (value h ds 0 0 0) hd hlen (by simpa using htotal)
    (by omega) (by omega) (by omega) (by omega)
    (le_max_left _ _) (by omega)

/-- Original positive-size units: K=h+1 and both capacities gain one. -/
theorem original_additive_guarantee {h : ℤ} (hh : 1 ≤ h) {m k : ℕ} {ds : List ℤ} {C : ℤ}
    (hd : ∀ d ∈ ds, 0 ≤ d) (hlen : ds.length=m+k) (htotal : ds.sum=h*m)
    (run : Run h m k ds 0 0 0 C) :
    C+1 ≤ (value h ds 0 0 0+1)+(h+1)-2 := by
  have := approximation hh hd hlen htotal run
  omega

#print axioms Gasoline.Integer.approximation
#print axioms Gasoline.Integer.original_additive_guarantee
end Gasoline.Integer

namespace Gasoline.Integer
/-- The inductive algorithm really yields a feasible schedule of its reported capacity. -/
theorem run_has_band {h : ℤ} (hh : 0 ≤ h) {m k : ℕ} {ds : List ℤ} {s A B C : ℤ}
    (run : Run h m k ds s A B C) (htotal : ds.sum-s=h*m) :
    ∃ a b : ℝ, Gasoline.Band h (ds.map Int.cast) s A B a b ∧ b-a=(C:ℝ) := by
  induction run with
  | done s A B =>
    have hs : s=0 := by simp at htotal; omega
    refine ⟨A,B,⟨le_rfl,le_rfl,?_⟩,?_⟩
    · simp [Gasoline.Reach,hs]
    · push_cast; ring
  | @small m k d s A B C ds choose tail ih =>
    have ht : ds.sum-(s-d)=h*m := by simp only [List.sum_cons] at htotal; omega
    obtain ⟨a,b,hband,heq⟩ := ih ht
    simp only [Gasoline.Band,Int.cast_min,Int.cast_max,Int.cast_sub] at hband
    rcases hband with ⟨ha,hb,hr⟩
    have haA := le_trans ha (min_le_left _ _)
    have haS := le_trans ha (min_le_right _ _)
    have hBb := le_trans (le_max_left _ _) hb
    have hSb := le_trans (le_max_right _ _) hb
    refine ⟨a,b,⟨haA,hBb,?_⟩,heq⟩
    change ∃ z : ℝ, 0≤z ∧ z≤(h:ℝ) ∧ (s:ℝ)+z≤b ∧ a≤(s:ℝ)+z-d ∧
      Gasoline.Reach h (ds.map Int.cast) ((s:ℝ)+z-d) a b
    refine ⟨0,le_rfl,by exact_mod_cast hh,by simpa using hSb,by simpa using haS,?_⟩
    simpa using hr
  | @large m k d s A B C ds choose tail ih =>
    have ht : ds.sum-(s+h-d)=h*m := by
      simp only [List.sum_cons,Nat.cast_add,Nat.cast_one,mul_add,mul_one] at htotal
      omega
    obtain ⟨a,b,hband,heq⟩ := ih ht
    simp only [Gasoline.Band,Int.cast_min,Int.cast_max,Int.cast_sub,Int.cast_add] at hband
    rcases hband with ⟨ha,hb,hr⟩
    have haA := le_trans ha (min_le_left _ _)
    have haS := le_trans ha (min_le_right _ _)
    have hBb := le_trans (le_max_left _ _) hb
    have hSb := le_trans (le_max_right _ _) hb
    refine ⟨a,b,⟨haA,hBb,?_⟩,heq⟩
    change ∃ z : ℝ, 0≤z ∧ z≤(h:ℝ) ∧ (s:ℝ)+z≤b ∧ a≤(s:ℝ)+z-d ∧
      Gasoline.Reach h (ds.map Int.cast) ((s:ℝ)+z-d) a b
    exact ⟨h,by exact_mod_cast hh,le_rfl,hSb,haS,hr⟩
end Gasoline.Integer

namespace Gasoline.Integer
/-- The model is total: a legal minimum-score run exists for every input. -/
theorem run_exists (h : ℤ) (ds : List ℤ) (m k : ℕ) (s A B : ℤ)
    (hlen : ds.length=m+k) : ∃ C, Run h m k ds s A B C := by
  induction ds generalizing m k s A B with
  | nil =>
    have hm : m=0 := by simp at hlen; omega
    have hk : k=0 := by simp at hlen; omega
    subst m; subst k
    exact ⟨B-A,Run.done s A B⟩
  | cons d ds ih =>
    cases m with
    | zero =>
      cases k with
      | zero => simp at hlen
      | succ k =>
        obtain ⟨C,hr⟩ := ih 0 k (s-d) (min A (s-d)) (max B s) (by simp at hlen; omega)
        exact ⟨C,Run.small (Or.inl rfl) hr⟩
    | succ m =>
      cases k with
      | zero =>
        obtain ⟨C,hr⟩ := ih m 0 (s+h-d) (min A (s+h-d)) (max B (s+h)) (by simp at hlen; omega)
        exact ⟨C,Run.large (Or.inl rfl) hr⟩
      | succ k =>
        by_cases hc : score h d ds s A B 0 ≤ score h d ds s A B h
        · obtain ⟨C,hr⟩ := ih (m+1) k (s-d) (min A (s-d)) (max B s) (by simp at hlen; omega)
          exact ⟨C,Run.small (Or.inr hc) hr⟩
        · obtain ⟨C,hr⟩ := ih m (k+1) (s+h-d) (min A (s+h-d)) (max B (s+h)) (by simp at hlen; omega)
          exact ⟨C,Run.large (Or.inr (by omega)) hr⟩
end Gasoline.Integer
