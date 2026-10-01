import Reachability

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000

namespace Gasoline
namespace Integer

def budget (h : ℤ) : List ℤ → ℤ
  | [] => 0
  | _ :: ds => h + budget h ds

def deficit (h : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: ds => max 0 (d-h+deficit h ds)

def terminal (h : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: ds => max (terminal h ds) (ds.sum+d-budget h ds)

def internal (h : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: ds => max (internal h ds) (d+deficit h ds)

def value (h : ℤ) (ds : List ℤ) (s A B : ℤ) : ℤ :=
  max (internal h ds) (max B (terminal h ds)-min A (s-deficit h ds))

def score (h d : ℤ) (ds : List ℤ) (s A B z : ℤ) : ℤ :=
  value h ds (s+z-d) (min A (s+z-d)) (max B (s+z))

lemma deficit_nonneg (h : ℤ) (ds : List ℤ) : 0 ≤ deficit h ds := by
  cases ds <;> simp [deficit]

lemma cast_budget (h : ℤ) (ds : List ℤ) :
    (budget h ds : ℝ) = Gasoline.budget h (ds.map Int.cast) := by
  induction ds with
  | nil => simp [budget, Gasoline.budget]
  | cons d ds ih => simp [budget, Gasoline.budget, ih]

lemma cast_summary (h : ℤ) (ds : List ℤ) :
    (deficit h ds : ℝ) = Gasoline.deficit h (ds.map Int.cast) ∧
    (terminal h ds : ℝ) = Gasoline.terminal h (ds.map Int.cast) ∧
    (internal h ds : ℝ) = Gasoline.internal h (ds.map Int.cast) := by
  induction ds with
  | nil => simp [deficit, terminal, internal, Gasoline.deficit, Gasoline.terminal, Gasoline.internal]
  | cons d ds ih =>
    simp [deficit, terminal, internal, Gasoline.deficit, Gasoline.terminal,
      Gasoline.internal, ← ih.1, ← ih.2.1, ← ih.2.2, ← cast_budget]

lemma cast_value (h : ℤ) (ds : List ℤ) (s A B : ℤ) :
    (value h ds s A B : ℝ) = Gasoline.prefixValue h (ds.map Int.cast) s A B := by
  rcases cast_summary h ds with ⟨hd,ht,hv⟩
  simp [value, Gasoline.prefixValue, ← hd, ← ht, ← hv]

/-- Closed form for the LP score after fixing the next supply. -/
theorem score_formula (h d : ℤ) (ds : List ℤ) (s A B z : ℤ)
    (hz : 0 ≤ z) (hAs : A ≤ s) :
    score h d ds s A B z =
      max (max (internal h ds) (max (max B (terminal h ds)-A) (d+deficit h ds)))
          (max (max B (terminal h ds)+d+deficit h ds-s-z) (s-A+z)) := by
  have hD := deficit_nonneg h ds
  unfold score value
  omega

/-- The key integer step: both candidate scores cannot exceed the bound. -/
theorem both_choices_bound (h d L0 : ℤ) (ds : List ℤ) (s A B : ℤ)
    (hh : 1 ≤ h) (hAs : A ≤ s) (hsB : s ≤ B)
    (hL : value h (d::ds) s A B ≤ L0+h-1)
    (hV : internal h (d::ds) ≤ L0) :
    min (score h d ds s A B 0) (score h d ds s A B h) ≤ L0+h-1 := by
  let R := d+deficit h ds
  let W := max B (terminal h ds)
  let F := max (internal h ds) (max (W-A) R)
  let u := W+R-s
  let v := s-A
  let C := value h (d::ds) s A B
  have cV : max (internal h ds) R ≤ C := le_max_left _ _
  have cRange : max B (terminal h (d::ds))-min A (s-deficit h (d::ds)) ≤ C := le_max_right _ _
  have wle : W ≤ max B (terminal h (d::ds)) := by
    dsimp [W,terminal]
    omega
  have mle : min A (s-deficit h (d::ds)) ≤ A := min_le_left _ _
  have rle : R ≤ C := le_trans (le_max_right _ _) cV
  have vle : internal h ds ≤ C := le_trans (le_max_left _ _) cV
  have fle : F ≤ C := by dsimp [F]; apply max_le vle; apply max_le; omega; exact rle
  have dge : d-h+deficit h ds ≤ deficit h (d::ds) := le_max_right _ _
  have mle2 : min A (s-deficit h (d::ds)) ≤ s-deficit h (d::ds) := min_le_right _ _
  have ule : u-h ≤ C := by dsimp [u,W,R]; dsimp [W] at wle; omega
  have vlF : v ≤ F := by
    have hf : W-A ≤ F := le_trans (le_max_left _ _) (le_max_right _ _)
    have hbW : B ≤ W := le_max_left _ _
    dsimp [v]; omega
  have rL : R ≤ L0 := le_trans (le_max_right _ _) hV
  have sumle : u+v ≤ F+L0 := by
    have hf : W-A ≤ F := le_trans (le_max_left _ _) (le_max_right _ _)
    dsimp [u,v]; omega
  have small : score h d ds s A B 0 = max F (max u v) := by
    rw [score_formula h d ds s A B 0 (by omega) hAs]
    dsimp [F,u,v,W,R]; congr 2 <;> omega
  have large : score h d ds s A B h = max F (max (u-h) (v+h)) := by
    rw [score_formula h d ds s A B h (by omega) hAs]
    dsimp [F,u,v,W,R]; congr 2 <;> omega
  rw [small,large]
  change C ≤ L0+h-1 at hL
  omega

#print axioms Gasoline.Integer.score_formula
#print axioms Gasoline.Integer.both_choices_bound
end Integer
end Gasoline

namespace Gasoline.Integer
lemma budget_length (h : ℤ) (ds : List ℤ) : budget h ds = h * ds.length := by
  induction ds with
  | nil => simp [budget]
  | cons d ds ih => simp [budget,ih]; ring

lemma cast_sum (ds : List ℤ) : (ds.sum : ℝ) = (ds.map Int.cast).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [ih]

lemma forced_score (h d : ℤ) (ds : List ℤ) (s A B q : ℤ)
    (hh : 0 ≤ h) (hd0 : 0 ≤ d) (hd : ∀ e ∈ ds, 0 ≤ e)
    (hA : A ≤ 0) (hB : 0 ≤ B) (hAs : A ≤ s) (hsB : s ≤ B)
    (he0 : 0 ≤ (d::ds).sum-s) (heN : (d::ds).sum-s ≤ budget h (d::ds))
    (hf : (q=0 ∧ (d::ds).sum-s=0) ∨ (q=h ∧ (d::ds).sum-s=budget h (d::ds))) :
    score h d ds s A B q ≤ value h (d::ds) s A B := by
  have hdR : ∀ e ∈ ds.map (Int.cast : ℤ → ℝ), 0 ≤ e := by
    intro e he
    rcases List.mem_map.mp he with ⟨x,hx,rfl⟩
    exact_mod_cast hd x hx
  have he0R : 0 ≤ (((d::ds).map Int.cast).sum : ℝ)-s := by rw [← cast_sum]; exact_mod_cast he0
  have heNR : (((d::ds).map Int.cast).sum : ℝ)-s ≤ Gasoline.budget h ((d::ds).map Int.cast) := by
    rw [← cast_sum, ← cast_budget]; exact_mod_cast heN
  have hfR : ((q:ℝ)=0 ∧ (((d::ds).map Int.cast).sum : ℝ)-s=0) ∨
      ((q:ℝ)=h ∧ (((d::ds).map Int.cast).sum : ℝ)-s=Gasoline.budget h ((d::ds).map Int.cast)) := by
    rw [← cast_sum,← cast_budget]
    exact_mod_cast hf
  have H := Gasoline.forced_step (by exact_mod_cast hh) (by exact_mod_cast hd0)
    (ds.map Int.cast) hdR (s:ℝ) (A:ℝ) (B:ℝ) (q:ℝ)
    (by exact_mod_cast hA) (by exact_mod_cast hB) (by exact_mod_cast hAs) (by exact_mod_cast hsB)
    he0R heNR hfR
  have H' : (score h d ds s A B q : ℝ) ≤ (value h (d::ds) s A B : ℝ) := by
    simpa [score,cast_value] using H
  exact_mod_cast H'
end Gasoline.Integer
