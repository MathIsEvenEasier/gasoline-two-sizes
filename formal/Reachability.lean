import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace Gasoline

/-- Fractional supply budget for a list of remaining demand slots. -/
def budget (h : ℝ) : List ℝ → ℝ
  | [] => 0
  | _ :: ds => h + budget h ds

def deficit (h : ℝ) : List ℝ → ℝ
  | [] => 0
  | d :: ds => max 0 (d - h + deficit h ds)

def terminal (h : ℝ) : List ℝ → ℝ
  | [] => 0
  | d :: ds => max (terminal h ds) (ds.sum + d - budget h ds)

def internal (h : ℝ) : List ℝ → ℝ
  | [] => 0
  | d :: ds => max (internal h ds) (d + deficit h ds)

/-- Actual fractional delivery choices, with both peak and trough constraints.
The last inventory is zero. No LP-value formula is built into this definition. -/
def Reach (h : ℝ) : List ℝ → ℝ → ℝ → ℝ → Prop
  | [], s, _, _ => s = 0
  | d :: ds, s, a, b => ∃ z : ℝ, 0 ≤ z ∧ z ≤ h ∧ s + z ≤ b ∧
      a ≤ s + z - d ∧ Reach h ds (s + z - d) a b

lemma budget_nonneg {h : ℝ} (hh : 0 ≤ h) (ds : List ℝ) : 0 ≤ budget h ds := by
  induction ds with
  | nil => simp [budget]
  | cons d ds ih => simp only [budget]; linarith

lemma deficit_nonneg (h : ℝ) (ds : List ℝ) : 0 ≤ deficit h ds := by
  cases ds <;> simp [deficit]

lemma deficit_le_sum {h : ℝ} (hh : 0 ≤ h) (ds : List ℝ)
    (hd : ∀ d ∈ ds, 0 ≤ d) : deficit h ds ≤ ds.sum := by
  induction ds with
  | nil => simp [deficit]
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e := by intro e he; exact hd e (by simp [he])
    have ih' := ih hds
    have hn := deficit_nonneg h ds
    simp only [deficit, List.sum_cons, max_le_iff]
    constructor <;> linarith

/-- Exact real feasibility of a fractional continuation in an inventory band. -/
theorem reach_iff {h : ℝ} (hh : 0 ≤ h) (ds : List ℝ)
    (hd : ∀ d ∈ ds, 0 ≤ d) (s a b : ℝ)
    (ha : a ≤ 0) (hb : 0 ≤ b) (has : a ≤ s) (hsb : s ≤ b) :
    Reach h ds s a b ↔
      internal h ds ≤ b-a ∧ a ≤ s-deficit h ds ∧ terminal h ds ≤ b ∧
      0 ≤ ds.sum-s ∧ ds.sum-s ≤ budget h ds := by
  induction ds generalizing s with
  | nil =>
    simp only [Reach, internal, deficit, terminal, List.sum_nil, budget]
    constructor
    · intro hx
      subst s
      exact ⟨by linarith, by simpa using ha, hb, by simp, by simp⟩
    · rintro ⟨_,_,_,h1,h2⟩
      linarith 
  | cons d ds ih =>
    have hd0 : 0 ≤ d := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e := by intro e he; exact hd e (by simp [he])
    have hD := deficit_nonneg h ds
    have hDE := deficit_le_sum hh ds hds
    have hN := budget_nonneg hh ds
    simp only [Reach, internal, deficit, terminal, List.sum_cons, budget]
    constructor
    · rintro ⟨z,hz0,hzh,hpeak,htrough,htail⟩
      have hstate : s+z-d ≤ b := by linarith
      have H := (ih hds (s+z-d) htrough hstate).mp htail
      rcases H with ⟨hV,hD',hT,hE0,hEN⟩
      refine ⟨?_,?_,?_,?_,?_⟩
      · apply max_le <;> linarith
      · have h1 : 0 ≤ s-a := by linarith
        have h2 : d-h+deficit h ds ≤ s-a := by linarith
        have hm := max_le h1 h2
        linarith
      · apply max_le <;> linarith
      · linarith
      · linarith
    · rintro ⟨hV,hD',hT,hE0,hEN⟩
      have hv1 := (max_le_iff.mp hV).1
      have hv2 := (max_le_iff.mp hV).2
      have ht1 := (max_le_iff.mp hT).1
      have ht2 := (max_le_iff.mp hT).2
      have hdx : d-h+deficit h ds ≤ max 0 (d-h+deficit h ds) := le_max_right _ _
      let z := max 0 (max (a+d+deficit h ds-s) (ds.sum+d-s-budget h ds))
      have hz0 : 0 ≤ z := le_max_left _ _
      have hzA : a+d+deficit h ds-s ≤ z := le_trans (le_max_left _ _) (le_max_right _ _)
      have hzN : ds.sum+d-s-budget h ds ≤ z := le_trans (le_max_right _ _) (le_max_right _ _)
      have hzh : z ≤ h := by dsimp [z]; apply max_le hh; apply max_le <;> linarith
      have hzB : z ≤ b-s := by dsimp [z]; apply max_le; linarith; apply max_le <;> linarith
      have hzE : z ≤ ds.sum+d-s := by dsimp [z]; apply max_le; linarith; apply max_le <;> linarith
      have htrough : a ≤ s+z-d := by linarith
      have hstate : s+z-d ≤ b := by linarith
      refine ⟨z,hz0,hzh,by linarith,htrough,?_⟩
      apply (ih hds (s+z-d) htrough hstate).mpr
      exact ⟨hv1,by linarith,ht1,by linarith,by linarith⟩

end Gasoline

namespace Gasoline

def prefixValue (h : ℝ) (ds : List ℝ) (s A B : ℝ) : ℝ :=
  max (internal h ds) (max B (terminal h ds) - min A (s-deficit h ds))

def Band (h : ℝ) (ds : List ℝ) (s A B a b : ℝ) : Prop :=
  a ≤ A ∧ B ≤ b ∧ Reach h ds s a b

theorem prefix_lower {h : ℝ} (hh : 0 ≤ h) (ds : List ℝ)
    (hd : ∀ d ∈ ds, 0 ≤ d) (s A B a b : ℝ)
    (hA : A ≤ 0) (hB : 0 ≤ B) (hAs : A ≤ s) (hsB : s ≤ B)
    (H : Band h ds s A B a b) : prefixValue h ds s A B ≤ b-a := by
  rcases H with ⟨ha,hb,hr⟩
  have H := (reach_iff hh ds hd s a b (by linarith) (by linarith)
    (by linarith) (by linarith)).mp hr
  rcases H with ⟨hv,hd',ht,_,_⟩
  have hmin : a ≤ min A (s-deficit h ds) := le_min ha hd'
  have hmax : max B (terminal h ds) ≤ b := max_le hb ht
  exact max_le hv (by linarith)

theorem prefix_attained {h : ℝ} (hh : 0 ≤ h) (ds : List ℝ)
    (hd : ∀ d ∈ ds, 0 ≤ d) (s A B : ℝ)
    (hA : A ≤ 0) (hB : 0 ≤ B) (hAs : A ≤ s) (hsB : s ≤ B)
    (he0 : 0 ≤ ds.sum-s) (heN : ds.sum-s ≤ budget h ds) :
    ∃ a b, Band h ds s A B a b ∧ b-a = prefixValue h ds s A B := by
  let a := min A (s-deficit h ds)
  let C := prefixValue h ds s A B
  have haA : a ≤ A := min_le_left _ _
  have haD : a ≤ s-deficit h ds := min_le_right _ _
  have hCV : internal h ds ≤ C := le_max_left _ _
  have hCM : max B (terminal h ds)-a ≤ C := le_max_right _ _
  have hCB : B ≤ a+C := by have := le_max_left B (terminal h ds); linarith
  have hCT : terminal h ds ≤ a+C := by have := le_max_right B (terminal h ds); linarith
  refine ⟨a,a+C,⟨haA,hCB,?_⟩,by dsimp [C]; ring⟩
  apply (reach_iff hh ds hd s a (a+C) (by linarith) (by linarith)
    (by linarith) (by linarith)).mpr
  exact ⟨by linarith,haD,hCT,he0,heN⟩

#print axioms Gasoline.reach_iff
#print axioms Gasoline.prefix_lower
#print axioms Gasoline.prefix_attained
end Gasoline

namespace Gasoline
/-- If only one supply size remains, fixing it does not increase the exact LP. -/
theorem forced_step {h d : ℝ} (hh : 0 ≤ h) (hd0 : 0 ≤ d) (ds : List ℝ)
    (hd : ∀ e ∈ ds, 0 ≤ e) (s A B q : ℝ)
    (hA : A ≤ 0) (hB : 0 ≤ B) (hAs : A ≤ s) (hsB : s ≤ B)
    (he0 : 0 ≤ (d::ds).sum-s) (heN : (d::ds).sum-s ≤ budget h (d::ds))
    (hf : (q=0 ∧ (d::ds).sum-s=0) ∨ (q=h ∧ (d::ds).sum-s=budget h (d::ds))) :
    prefixValue h ds (s+q-d) (min A (s+q-d)) (max B (s+q)) ≤
      prefixValue h (d::ds) s A B := by
  have hall : ∀ e ∈ d::ds, 0 ≤ e := by simpa using And.intro hd0 hd
  obtain ⟨a,b,⟨haA,hBb,hr⟩,heq⟩ := prefix_attained hh (d::ds) hall s A B hA hB hAs hsB he0 heN
  rcases hr with ⟨z,hz0,hzh,hpeak,htrough,htail⟩
  have hstate : s+z-d ≤ b := by linarith
  have HT := (reach_iff hh ds hd (s+z-d) a b (by linarith) (by linarith) htrough hstate).mp htail
  have hzq : z=q := by
    rcases hf with ⟨hq,he⟩ | ⟨hq,he⟩
    · simp only [List.sum_cons] at he
      have := HT.2.2.2.1
      linarith
    · simp only [List.sum_cons,budget] at he
      have := HT.2.2.2.2
      linarith
  subst z
  have hband : Band h ds (s+q-d) (min A (s+q-d)) (max B (s+q)) a b :=
    ⟨le_min haA htrough,max_le hBb hpeak,htail⟩
  have hnew := prefix_lower hh ds hd (s+q-d) (min A (s+q-d)) (max B (s+q)) a b
    (le_trans (min_le_left _ _) hA) (le_trans hB (le_max_left _ _))
    (min_le_right _ _) (by have := le_max_right B (s+q); linarith) hband
  linarith
end Gasoline
