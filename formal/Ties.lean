import Rounding
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Gasoline.Integer
/-- A run that always chooses the first remaining input item. The item is a
minimum-score candidate, so the original-index tie rule must select it. -/
inductive HeadRun (h : ℤ) : List ℤ → List ℤ → ℤ → ℤ → ℤ → ℤ → Prop
  | done (s A B : ℤ) : HeadRun h [] [] s A B (B-A)
  | step {d q s A B C : ℤ} {ds qs : List ℤ}
      (best : ∀ v ∈ q::qs, score h d ds s A B q ≤ score h d ds s A B v)
      (tail : HeadRun h ds qs (s+q-d) (min A (s+q-d)) (max B (s+q)) C) :
      HeadRun h (d::ds) (q::qs) s A B C

/-- Every allowed tie path is realized by an input order for first-index ties. -/
theorem run_realizable {h : ℤ} (hh : 1 ≤ h) {m k : ℕ} {ds : List ℤ} {s A B C : ℤ}
    (run : Run h m k ds s A B C) :
    ∃ qs, HeadRun h ds qs s A B C ∧ (∀ q ∈ qs, q=0 ∨ q=h) ∧
      qs.count h=m ∧ qs.count 0=k := by
  have hn : h ≠ 0 := by omega
  induction run with
  | done s A B => exact ⟨[],HeadRun.done s A B,by simp,by simp,by simp⟩
  | @small m k d s A B C ds choose tail ih =>
    obtain ⟨qs,hr,hqs,hm,hk⟩ := ih
    refine ⟨0::qs,?_,?_,?_,?_⟩
    · refine HeadRun.step ?_ ?_
      · intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · subst v; exact le_rfl
        · rcases hqs v hv with hz | hh'
          · subst v; exact le_rfl
          · subst v
            rcases choose with he | hc
            · have hnot : h ∉ qs := by exact List.count_eq_zero.mp (by simpa [he] using hm)
              exact False.elim (hnot hv)
            · exact hc
      · simpa using hr
    · intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · exact Or.inl hv
      · exact hqs v hv
    · simpa [List.count_cons,hn,Ne.symm hn] using hm
    · simp [hk]
  | @large m k d s A B C ds choose tail ih =>
    obtain ⟨qs,hr,hqs,hm,hk⟩ := ih
    refine ⟨h::qs,?_,?_,?_,?_⟩
    · refine HeadRun.step ?_ hr
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v; exact le_rfl
      · rcases hqs v hv with hz | hh'
        · subst v
          rcases choose with he | hc
          · have hnot : 0 ∉ qs := by exact List.count_eq_zero.mp (by simpa [he] using hk)
            exact False.elim (hnot hv)
          · exact hc
        · subst v; exact le_rfl
    · intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · exact Or.inr hv
      · exact hqs v hv
    · simp [hm]
    · simpa [List.count_cons,hn,Ne.symm hn] using hk

#print axioms Gasoline.Integer.run_realizable
end Gasoline.Integer
