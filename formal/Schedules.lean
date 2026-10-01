import Rounding
set_option linter.unusedVariables false

namespace Gasoline.Integer
/-- An arbitrary integral comparison schedule, with no greedy restriction. -/
inductive Schedule (h : ℤ) : ℕ → ℕ → List ℤ → ℤ → ℤ → ℤ → Prop
  | done (a b : ℤ) : Schedule h 0 0 [] 0 a b
  | small {m k : ℕ} {d s a b : ℤ} {ds : List ℤ}
      (peak : s ≤ b) (trough : a ≤ s-d) (tail : Schedule h m k ds (s-d) a b) :
      Schedule h m (k+1) (d::ds) s a b
  | large {m k : ℕ} {d s a b : ℤ} {ds : List ℤ}
      (peak : s+h ≤ b) (trough : a ≤ s+h-d) (tail : Schedule h m k ds (s+h-d) a b) :
      Schedule h (m+1) k (d::ds) s a b

lemma Schedule.relax {h : ℤ} (hh : 0 ≤ h) {m k : ℕ} {ds : List ℤ} {s a b : ℤ}
    (I : Schedule h m k ds s a b) : Gasoline.Reach h (ds.map Int.cast) s a b := by
  induction I with
  | done a b => simp [Gasoline.Reach]
  | @small m k d s a b ds hp ht tail ih =>
    refine ⟨0,by norm_num,by exact_mod_cast hh,by simpa using (show (s:ℝ)≤b by exact_mod_cast hp),?_,?_⟩
    · simpa using (show (a:ℝ)≤(s:ℝ)-d by exact_mod_cast ht)
    · simpa using ih
  | @large m k d s a b ds hp ht tail ih =>
    refine ⟨(h:ℝ),by exact_mod_cast hh,le_rfl,by exact_mod_cast hp,by exact_mod_cast ht,?_⟩
    simpa using ih

lemma Schedule.large_lower {h : ℤ} {m k : ℕ} {ds : List ℤ} {s a b : ℤ}
    (I : Schedule h m k ds s a b) (hm : 0<m) (ha : a≤s) : h≤b-a := by
  induction I with
  | done => omega
  | small hp ht tail ih => exact ih hm ht
  | large hp ht tail ih => omega

lemma run_has_schedule {h : ℤ} {m k : ℕ} {ds : List ℤ} {s A B C : ℤ}
    (run : Run h m k ds s A B C) (htotal : ds.sum-s=h*m) :
    ∃ a b : ℤ, a≤A ∧ B≤b ∧ Schedule h m k ds s a b ∧ b-a=C := by
  induction run with
  | done s A B =>
    have hs : s=0 := by simp at htotal; omega
    subst s
    exact ⟨A,B,le_rfl,le_rfl,Schedule.done A B,rfl⟩
  | @small m k d s A B C ds choose tail ih =>
    have ht : ds.sum-(s-d)=h*m := by simp only [List.sum_cons] at htotal; omega
    obtain ⟨a,b,ha,hb,hs,he⟩ := ih ht
    refine ⟨a,b,?_,?_,Schedule.small ?_ ?_ hs,he⟩ <;> omega
  | @large m k d s A B C ds choose tail ih =>
    have ht : ds.sum-(s+h-d)=h*m := by
      simp only [List.sum_cons,Nat.cast_add,Nat.cast_one,mul_add,mul_one] at htotal
      omega
    obtain ⟨a,b,ha,hb,hs,he⟩ := ih ht
    refine ⟨a,b,?_,?_,Schedule.large ?_ ?_ hs,he⟩ <;> omega

/-- Every integral schedule is bounded below by the exact fractional value. -/
theorem schedule_lower {h : ℤ} (hh : 0 ≤ h) {m k : ℕ} {ds : List ℤ} {a b : ℤ}
    (hd : ∀ d ∈ ds, 0 ≤ d) (ha : a≤0) (hb : 0≤b)
    (I : Schedule h m k ds 0 a b) : value h ds 0 0 0 ≤ b-a := by
  have hdR : ∀ d ∈ ds.map (Int.cast : ℤ → ℝ), 0 ≤ d := by
    intro d he
    rcases List.mem_map.mp he with ⟨e,hmem,rfl⟩
    exact_mod_cast hd e hmem
  have HR := I.relax hh
  have H := Gasoline.prefix_lower (h := (h:ℝ)) (by exact_mod_cast hh) (ds.map Int.cast) hdR
    0 0 0 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨by exact_mod_cast ha,by exact_mod_cast hb,by simpa using HR⟩
  have HV : (value h ds 0 0 0 : ℝ) = Gasoline.prefixValue h (ds.map Int.cast) 0 0 0 := by
    simpa using cast_value h ds 0 0 0
  rw [← HV] at H
  exact_mod_cast H

/-- Comparison with any integral schedule; taking its minimum gives OPT. -/
theorem compared_to_schedule {h : ℤ} (hh : 1 ≤ h) {m k : ℕ} {ds : List ℤ} {C a b : ℤ}
    (hd : ∀ d ∈ ds, 0 ≤ d) (hlen : ds.length=m+k) (htotal : ds.sum=h*m)
    (run : Run h m k ds 0 0 0 C) (ha : a≤0) (hb : 0≤b)
    (I : Schedule h m k ds 0 a b) : C+1 ≤ (b-a+1)+(h+1)-2 := by
  have H := approximation hh hd hlen htotal run
  have L := schedule_lower (by omega) hd ha hb I
  omega

/-- Fixed-K ratio in division-free form: K*C_alg <= (2K-2)*C_comparison. -/
theorem ratio_bound {h : ℤ} (hh : 1 ≤ h) {m k : ℕ} {ds : List ℤ} {C a b : ℤ}
    (hm : 0<m) (hd : ∀ d ∈ ds, 0 ≤ d) (hlen : ds.length=m+k) (htotal : ds.sum=h*m)
    (run : Run h m k ds 0 0 0 C) (ha : a≤0) (hb : 0≤b)
    (I : Schedule h m k ds 0 a b) : (h+1)*(C+1) ≤ (2*h)*(b-a+1) := by
  have H := compared_to_schedule hh hd hlen htotal run ha hb I
  have L := I.large_lower hm ha
  nlinarith

#print axioms Gasoline.Integer.compared_to_schedule
#print axioms Gasoline.Integer.ratio_bound
end Gasoline.Integer
