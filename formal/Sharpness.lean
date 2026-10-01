import Rounding

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000

namespace Gasoline.Integer

def blocks (h j : ℤ) : ℕ → List ℤ
  | 0 => [h,h-1]
  | r+1 => (h-j-2)::(j+2)::blocks h (j+1) r

lemma blocks_summary (h j : ℤ) (r : ℕ) (hh : 2 ≤ h) (hj : 0 ≤ j)
    (hjr : j+r=h-2) :
    deficit h (blocks h j r)=0 ∧ terminal h (blocks h j r)=h-1 ∧
    internal h (blocks h j r)=h ∧ (blocks h j r).sum=h*(r+2)-1 ∧
    budget h (blocks h j r)=2*h*(r+1) := by
  induction r generalizing j with
  | zero =>
    simp only [blocks,deficit,terminal,internal,budget,List.sum_cons,List.sum_nil,Nat.cast_zero]
    constructor; omega
    constructor; omega
    constructor; omega
    constructor <;> ring
  | succ r ih =>
    have hjr' : (j+1)+(r:ℤ)=h-2 := by push_cast at hjr; omega
    rcases ih (j+1) (by omega) hjr' with ⟨hD,hT,hV,hE,hN⟩
    have hr : 0 ≤ (r:ℤ) := by positivity
    have hprod : 0 ≤ h*(r:ℤ) := by positivity
    have hjh : j+2 ≤ h := by omega
    simp only [blocks,deficit,terminal,internal,budget,List.sum_cons]
    rw [hD,hT,hV,hE,hN]
    have mz : max 0 (j+2-h+0)=0 := by omega
    rw [mz]
    constructor; omega
    constructor
    · have ht : max (h-1) (h*((r:ℤ)+2)-1+(j+2)-2*h*((r:ℤ)+1))=h-1 := by
        apply max_eq_left; nlinarith
      rw [ht]
      apply max_eq_left
      nlinarith
    constructor
    · omega
    constructor <;> push_cast <;> ring

lemma blocks_run (h j : ℤ) (r : ℕ) (hh : 2 ≤ h) (hj : 0 ≤ j)
    (hjr : j+r=h-2) :
    Run h (r+1) (r+1) (blocks h j r) (h-1) 0 (h+j) (2*h-1) := by
  induction r generalizing j with
  | zero =>
    have hjval : j=h-2 := by simpa using hjr
    subst j
    refine Run.small (Or.inr ?_) ?_
    · simp only [score,value,blocks,internal,terminal,deficit,budget,List.sum_cons,List.sum_nil]
      omega
    · apply Run.large (Or.inl rfl)
      convert Run.done (h:=h) 0 (-1) (2*h-2) using 1 <;> omega
  | succ r ih =>
    have hjr' : (j+1)+(r:ℤ)=h-2 := by push_cast at hjr; omega
    have hjh : j+2 ≤ h := by
      have hr : 0 ≤ (r:ℤ) := by positivity
      omega
    rcases blocks_summary h (j+1) r hh (by omega) hjr' with ⟨hD,hT,hV,hE,hN⟩
    have hd0 : 0 ≤ h-j-2 := by omega
    change Run h (r+1+1) (r+1+1) ((h-j-2)::(j+2)::blocks h (j+1) r) (h-1) 0 (h+j) (2*h-1)
    refine Run.small (Or.inr ?_) ?_
    · simp only [score,value,internal,terminal,deficit,budget,List.sum_cons]
      rw [hD,hT,hV,hE,hN]
      have hp : 0 ≤ h*(r:ℤ) := by positivity
      have ht : max (h-1) (h*((r:ℤ)+2)-1+(j+2)-2*h*((r:ℤ)+1))=h-1 := by
        apply max_eq_left; nlinarith
      rw [ht]
      omega
    · have e1 : h-1-(h-j-2)=j+1 := by omega
      have e2 : min 0 (j+1)=0 := by omega
      have e3 : max (h+j) (h-1)=h+j := by omega
      rw [e1,e2,e3]
      refine Run.large (Or.inr ?_) ?_
      · simp only [score,value]
        rw [hD,hT,hV]
        omega
      · have e4 : j+1+h-(j+2)=h-1 := by omega
        have e5 : min 0 (h-1)=0 := by omega
        have e6 : max (h+j) (j+1+h)=h+(j+1) := by omega
        rw [e4,e5,e6]
        exact ih (j+1) (by omega) hjr'

/-- Infinite family: r=K-3, h=K-1. The original input head is chosen at
all ties, so this run is realizable by original-index tie breaking. -/
theorem sharp_run (r : ℕ) :
    Run ((r:ℤ)+2) (r+2) (r+1) (1::blocks ((r:ℤ)+2) 0 r) 0 0 0 (2*((r:ℤ)+2)-1) := by
  let h : ℤ := (r:ℤ)+2
  have hh : 2 ≤ h := by dsimp [h]; omega
  rcases blocks_summary h 0 r hh (by omega) (by dsimp [h]; omega) with ⟨hD,hT,hV,hE,hN⟩
  refine Run.large (Or.inr ?_) ?_
  · simp only [score,value]
    rw [hD,hT,hV]
    dsimp [h] at *
    omega
  · have e1 : (0:ℤ)+h-1=h-1 := by omega
    change Run h (r+1) (r+1) (blocks h 0 r) (0+h-1) (min 0 (0+h-1)) (max 0 (0+h)) (2*h-1)
    rw [e1]
    have e2 : min 0 (h-1)=0 := by omega
    have e3 : max 0 (0+h)=h+0 := by omega
    rw [e2,e3]
    exact blocks_run h 0 r hh (by omega) (by dsimp [h]; omega)

#print axioms Gasoline.Integer.sharp_run
end Gasoline.Integer

namespace Gasoline.Integer
lemma optimal_blocks (h j : ℤ) (r : ℕ) (B : ℤ) (hh : 2 ≤ h) (hj : 0 ≤ j)
    (hjr : j+r=h-2) (hB0 : 0 ≤ B) (hBh : B ≤ h-1) :
    Run h (r+2) r (blocks h j r) (-1) (-1) B h := by
  induction r generalizing j B with
  | zero =>
    change Run h (1+1) 0 (h::[h-1]) (-1) (-1) B h
    apply Run.large (Or.inl rfl)
    have e1 : -1+h-h=(-1:ℤ) := by omega
    have e2 : max B (-1+h)=h-1 := by omega
    rw [e1,min_self,e2]
    apply Run.large (Or.inl rfl)
    convert Run.done (h:=h) 0 (-1) (h-1) using 1 <;> omega
  | succ r ih =>
    have hjr' : (j+1)+(r:ℤ)=h-2 := by push_cast at hjr; omega
    have hr : 0 ≤ (r:ℤ) := by positivity
    have hjh : j+2 ≤ h := by omega
    rcases blocks_summary h (j+1) r hh (by omega) hjr' with ⟨hD,hT,hV,hE,hN⟩
    change Run h (r+2+1) (r+1) ((h-j-2)::(j+2)::blocks h (j+1) r) (-1) (-1) B h
    refine Run.large (Or.inr ?_) ?_
    · simp only [score,value,internal,terminal,deficit,budget,List.sum_cons]
      rw [hD,hT,hV,hE,hN]
      have hp : 0 ≤ h*(r:ℤ) := by positivity
      have ht : max (h-1) (h*((r:ℤ)+2)-1+(j+2)-2*h*((r:ℤ)+1))=h-1 := by
        apply max_eq_left; nlinarith
      rw [ht]
      omega
    · have e1 : -1+h-(h-j-2)=j+1 := by omega
      have e2 : min (-1) (j+1)=(-1:ℤ) := by omega
      have e3 : max B (-1+h)=h-1 := by omega
      rw [e1,e2,e3]
      refine Run.small (Or.inr ?_) ?_
      · simp only [score,value]
        rw [hD,hT,hV]
        omega
      · have e4 : j+1-(j+2)=(-1:ℤ) := by omega
        have e5 : max (h-1) (j+1)=h-1 := by omega
        rw [e4,min_self,e5]
        exact ih (j+1) (h-1) (by omega) hjr' (by omega) (by omega)

theorem optimal_run (r : ℕ) :
    Run ((r:ℤ)+2) (r+2) (r+1) (1::blocks ((r:ℤ)+2) 0 r) 0 0 0 ((r:ℤ)+2) := by
  let h : ℤ := (r:ℤ)+2
  have hh : 2 ≤ h := by dsimp [h]; omega
  rcases blocks_summary h 0 r hh (by omega) (by dsimp [h]; omega) with ⟨hD,hT,hV,hE,hN⟩
  refine Run.small (Or.inr ?_) ?_
  · simp only [score,value]
    rw [hD,hT,hV]
    dsimp [h] at *
    omega
  · change Run h (r+2) r (blocks h 0 r) (-1) (-1) 0 h
    exact optimal_blocks h 0 r 0 hh (by omega) (by dsimp [h]; omega) (by omega) (by omega)

lemma blocks_valid (h j : ℤ) (r : ℕ) (hh : 2 ≤ h) (hj : 0 ≤ j)
    (hjr : j+r=h-2) : (∀ d ∈ blocks h j r, 0 ≤ d) ∧ (blocks h j r).length=2*r+2 := by
  induction r generalizing j with
  | zero => simp [blocks]; omega
  | succ r ih =>
    have hjr' : (j+1)+(r:ℤ)=h-2 := by push_cast at hjr; omega
    have hr : 0 ≤ (r:ℤ) := by positivity
    rcases ih (j+1) (by omega) hjr' with ⟨hd,hn⟩
    simp only [blocks,List.mem_cons,forall_eq_or_imp,List.length_cons,hn]
    constructor
    · exact ⟨by omega,by omega,hd⟩
    · omega

theorem sharp_initial_value (r : ℕ) :
    value ((r:ℤ)+2) (1::blocks ((r:ℤ)+2) 0 r) 0 0 0 = (r:ℤ)+2 := by
  let h : ℤ := (r:ℤ)+2
  have hh : 2 ≤ h := by dsimp [h]; omega
  rcases blocks_summary h 0 r hh (by omega) (by dsimp [h]; omega) with ⟨hD,hT,hV,hE,hN⟩
  change value h (1::blocks h 0 r) 0 0 0=h
  simp only [value,internal,terminal,deficit,budget,List.sum_cons]
  rw [hD,hT,hV,hE,hN]
  have hp : 0 ≤ h*(r:ℤ) := by positivity
  have ht : max (h-1) (h*((r:ℤ)+2)-1+1-2*h*((r:ℤ)+1))=h-1 := by
    apply max_eq_left; nlinarith
  rw [ht]
  omega

/-- For every K=r+3: the input is valid, its exact relaxation is K-1,
and actual runs attain K-1 and 2K-3 in normalized capacity. -/
theorem sharp_family (r : ℕ) :
    let h : ℤ := (r:ℤ)+2
    let ds := 1::blocks h 0 r
    (∀ d ∈ ds, 0 ≤ d) ∧ ds.length=(r+2)+(r+1) ∧ ds.sum=h*(r+2) ∧
    value h ds 0 0 0=h ∧ Run h (r+2) (r+1) ds 0 0 0 h ∧
    Run h (r+2) (r+1) ds 0 0 0 (2*h-1) := by
  dsimp
  have hh : 2 ≤ (r:ℤ)+2 := by omega
  rcases blocks_valid ((r:ℤ)+2) 0 r hh (by omega) (by omega) with ⟨hd,hn⟩
  rcases blocks_summary ((r:ℤ)+2) 0 r hh (by omega) (by omega) with ⟨_,_,_,he,_⟩
  refine ⟨?_,?_,?_,sharp_initial_value r,optimal_run r,sharp_run r⟩
  · simpa using And.intro (by norm_num : (0:ℤ) ≤ 1) hd
  · simp [hn]; omega
  · simp only [List.sum_cons,he]; ring

#print axioms Gasoline.Integer.sharp_family
end Gasoline.Integer
