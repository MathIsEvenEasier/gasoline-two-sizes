import AssignmentLP
import Schedules
import Ties

set_option maxHeartbeats 2000000

namespace Gasoline.Integer

/-- Reachable-prefix invariants; no optimum formula is among the assumptions. -/
structure ValidPrefix (h : ℤ) (m k : ℕ) (ds : List ℤ) (s A B : ℤ) : Prop where
  demand_nonneg : ∀ d ∈ ds, 0 ≤ d
  length_eq : ds.length=m+k
  total_eq : ds.sum-s=h*m
  lower_zero : A≤0
  upper_zero : 0≤B
  lower_state : A≤s
  upper_state : s≤B

lemma ValidPrefix.small {h d s A B : ℤ} {m k : ℕ} {ds : List ℤ}
    (v : ValidPrefix h m (k+1) (d::ds) s A B) :
    ValidPrefix h m k ds (s-d) (min A (s-d)) (max B s) := by
  refine ⟨?_,?_,?_,le_trans (min_le_left _ _) v.lower_zero,
    le_trans v.upper_zero (le_max_left _ _),min_le_right _ _,?_⟩
  · intro e he; exact v.demand_nonneg e (by simp [he])
  · have := v.length_eq; simp only [List.length_cons] at this; omega
  · have := v.total_eq; simp only [List.sum_cons] at this; omega
  · have := v.demand_nonneg d (by simp)
    have := le_max_right B s
    omega

lemma ValidPrefix.large {h d s A B : ℤ} {m k : ℕ} {ds : List ℤ}
    (v : ValidPrefix h (m+1) k (d::ds) s A B) :
    ValidPrefix h m k ds (s+h-d) (min A (s+h-d)) (max B (s+h)) := by
  refine ⟨?_,?_,?_,le_trans (min_le_left _ _) v.lower_zero,
    le_trans v.upper_zero (le_max_left _ _),min_le_right _ _,?_⟩
  · intro e he; exact v.demand_nonneg e (by simp [he])
  · have := v.length_eq; simp only [List.length_cons] at this; omega
  · have := v.total_eq
    simp only [List.sum_cons,Nat.cast_add,Nat.cast_one,mul_add,mul_one] at this
    omega
  · have := v.demand_nonneg d (by simp)
    have := le_max_right B (s+h)
    omega

/-- Minimum of the original assignment LP, with integer input data cast to reals. -/
def StateLP (h : ℤ) (m k : ℕ) (ds : List ℤ) (s A B : ℤ) (v : ℝ) : Prop :=
  Gasoline.LPValue h m k (ds.map Int.cast) s A B v

lemma StateLP.unique {h s A B : ℤ} {m k : ℕ} {ds : List ℤ} {v w : ℝ}
    (hv : StateLP h m k ds s A B v) (hw : StateLP h m k ds s A B w) : v=w :=
  Gasoline.LPValue.unique hv hw

/-- Every valid residual LP is feasible, attains its minimum, and equals value+1. -/
theorem ValidPrefix.lp_value {h s A B : ℤ} {m k : ℕ} {ds : List ℤ}
    (v : ValidPrefix h m k ds s A B) (hh : 1≤h) :
    StateLP h m k ds s A B ((value h ds s A B:ℝ)+1) := by
  unfold StateLP
  rw [cast_value]
  apply Gasoline.matrixLP_value (by exact_mod_cast (show 0<h by omega)) m k
  · intro e he
    rcases List.mem_map.mp he with ⟨d,hd,rfl⟩
    exact_mod_cast v.demand_nonneg d hd
  · simpa using v.length_eq
  · rw [← cast_sum]
    exact_mod_cast v.total_eq
  · exact_mod_cast v.lower_zero
  · exact_mod_cast v.upper_zero
  · exact_mod_cast v.lower_state
  · exact_mod_cast v.upper_state

/-- Solve both candidate LPs and select a minimum. If only small items remain,
there is just one candidate size. All minima are allowed, including first-index ties. -/
def LPChooseSmall (h d : ℤ) (ds : List ℤ) (m k : ℕ) (s A B : ℤ) : Prop :=
  m=0 ∨ ∃ x y : ℝ,
    StateLP h m k ds (s-d) (min A (s-d)) (max B s) x ∧
    StateLP h (m-1) (k+1) ds (s+h-d) (min A (s+h-d)) (max B (s+h)) y ∧ x≤y

def LPChooseLarge (h d : ℤ) (ds : List ℤ) (m k : ℕ) (s A B : ℤ) : Prop :=
  k=0 ∨ ∃ x y : ℝ,
    StateLP h m k ds (s+h-d) (min A (s+h-d)) (max B (s+h)) x ∧
    StateLP h (m+1) (k-1) ds (s-d) (min A (s-d)) (max B s) y ∧ x≤y

/-- Algorithm 1's position-first minimum-LP rule, permitting any scan order for ties.
Unlike Run, this definition uses assignment matrices and their attained LP optima.
Counts are of remaining original sizes K=h+1 and 1. The state coordinates use
normalized demands d=y-1; C+1 is the original capacity for a nonempty instance. -/
inductive Algorithm1Run (h : ℤ) : ℕ → ℕ → List ℤ → ℤ → ℤ → ℤ → ℤ → Prop
  | done (s A B : ℤ) : Algorithm1Run h 0 0 [] s A B (B-A)
  | small {m k : ℕ} {d s A B C : ℤ} {ds : List ℤ}
      (choose : LPChooseSmall h d ds m k s A B)
      (tail : Algorithm1Run h m k ds (s-d) (min A (s-d)) (max B s) C) :
      Algorithm1Run h m (k+1) (d::ds) s A B C
  | large {m k : ℕ} {d s A B C : ℤ} {ds : List ℤ}
      (choose : LPChooseLarge h d ds m k s A B)
      (tail : Algorithm1Run h m k ds (s+h-d) (min A (s+h-d)) (max B (s+h)) C) :
      Algorithm1Run h (m+1) k (d::ds) s A B C

lemma small_choice_iff {h d s A B : ℤ} {m k : ℕ} {ds : List ℤ}
    (hh : 1≤h) (v : ValidPrefix h m (k+1) (d::ds) s A B) :
    (m=0 ∨ score h d ds s A B 0 ≤ score h d ds s A B h) ↔
      LPChooseSmall h d ds m k s A B := by
  cases m with
  | zero => simp [LPChooseSmall]
  | succ m =>
    have hs : StateLP h (m+1) k ds (s-d) (min A (s-d)) (max B s)
        ((score h d ds s A B 0:ℝ)+1) := by
      simpa [score] using v.small.lp_value hh
    have hl : StateLP h m (k+1) ds (s+h-d) (min A (s+h-d)) (max B (s+h))
        ((score h d ds s A B h:ℝ)+1) := by
      simpa [score] using v.large.lp_value hh
    simp only [LPChooseSmall,Nat.succ_ne_zero,false_or,Nat.succ_sub_one]
    constructor
    · intro hc
      refine ⟨_,_,hs,hl,?_⟩
      have : (score h d ds s A B 0:ℝ) ≤ score h d ds s A B h := by exact_mod_cast hc
      linarith
    · rintro ⟨x,y,hx,hy,hxy⟩
      have ex := hs.unique hx
      have ey := hl.unique hy
      have : (score h d ds s A B 0:ℝ) ≤ score h d ds s A B h := by linarith
      exact_mod_cast this

lemma large_choice_iff {h d s A B : ℤ} {m k : ℕ} {ds : List ℤ}
    (hh : 1≤h) (v : ValidPrefix h (m+1) k (d::ds) s A B) :
    (k=0 ∨ score h d ds s A B h ≤ score h d ds s A B 0) ↔
      LPChooseLarge h d ds m k s A B := by
  cases k with
  | zero => simp [LPChooseLarge]
  | succ k =>
    have hl : StateLP h m (k+1) ds (s+h-d) (min A (s+h-d)) (max B (s+h))
        ((score h d ds s A B h:ℝ)+1) := by
      simpa [score] using v.large.lp_value hh
    have hs : StateLP h (m+1) k ds (s-d) (min A (s-d)) (max B s)
        ((score h d ds s A B 0:ℝ)+1) := by
      simpa [score] using v.small.lp_value hh
    simp only [LPChooseLarge,Nat.succ_ne_zero,false_or,Nat.succ_sub_one]
    constructor
    · intro hc
      refine ⟨_,_,hl,hs,?_⟩
      have : (score h d ds s A B h:ℝ) ≤ score h d ds s A B 0 := by exact_mod_cast hc
      linarith
    · rintro ⟨x,y,hx,hy,hxy⟩
      have ex := hl.unique hx
      have ey := hs.unique hy
      have : (score h d ds s A B h:ℝ) ≤ score h d ds s A B 0 := by linarith
      exact_mod_cast this

/-- End-to-end bridge: the entire LP-based execution has exactly the same
possible capacities as Run, on every valid prefix. No score/LP correspondence
is assumed: it is proved above from actual assignment feasibility and attainment. -/
theorem run_iff_algorithm1 {h s A B C : ℤ} {m k : ℕ} {ds : List ℤ}
    (hh : 1≤h) (v : ValidPrefix h m k ds s A B) :
    Run h m k ds s A B C ↔ Algorithm1Run h m k ds s A B C := by
  constructor
  · intro run
    induction run with
    | done s A B => exact Algorithm1Run.done s A B
    | small choose tail ih =>
      exact Algorithm1Run.small ((small_choice_iff hh v).mp choose) (ih v.small)
    | large choose tail ih =>
      exact Algorithm1Run.large ((large_choice_iff hh v).mp choose) (ih v.large)
  · intro run
    induction run with
    | done s A B => exact Run.done s A B
    | small choose tail ih =>
      exact Run.small ((small_choice_iff hh v).mpr choose) (ih v.small)
    | large choose tail ih =>
      exact Run.large ((large_choice_iff hh v).mpr choose) (ih v.large)

/-- Algorithm 1, with actual LP candidate evaluations, inherits the proved
original-unit additive guarantee against every feasible comparison schedule. -/
theorem algorithm1_additive_guarantee {h C a b : ℤ} {m k : ℕ} {ds : List ℤ}
    (hh : 1≤h) (hd : ∀ d ∈ ds, 0≤d) (hlen : ds.length=m+k) (htotal : ds.sum=h*m)
    (run : Algorithm1Run h m k ds 0 0 0 C)
    (ha : a≤0) (hb : 0≤b) (I : Schedule h m k ds 0 a b) :
    C+1 ≤ (b-a+1)+(h+1)-2 := by
  have valid : ValidPrefix h m k ds 0 0 0 :=
    ⟨hd,hlen,by simpa using htotal,le_rfl,le_rfl,le_rfl,le_rfl⟩
  exact compared_to_schedule hh hd hlen htotal ((run_iff_algorithm1 hh valid).mpr run) ha hb I

/-- The sharper 2-2/K guarantee now explicitly applies to the assignment-LP rule. -/
theorem algorithm1_ratio_bound {h C a b : ℤ} {m k : ℕ} {ds : List ℤ}
    (hh : 1≤h) (hm : 0<m) (hd : ∀ d ∈ ds, 0≤d)
    (hlen : ds.length=m+k) (htotal : ds.sum=h*m)
    (run : Algorithm1Run h m k ds 0 0 0 C)
    (ha : a≤0) (hb : 0≤b) (I : Schedule h m k ds 0 a b) :
    (h+1)*(C+1) ≤ (2*h)*(b-a+1) := by
  have valid : ValidPrefix h m k ds 0 0 0 :=
    ⟨hd,hlen,by simpa using htotal,le_rfl,le_rfl,le_rfl,le_rfl⟩
  exact ratio_bound hh hm hd hlen htotal ((run_iff_algorithm1 hh valid).mpr run) ha hb I

/-- With no large item, every run follows the unique delivery sequence. -/
lemma run_no_large_le {h s A B C : ℤ} {m k : ℕ} {ds : List ℤ}
    (run : Run h m k ds s A B C) (hm : m=0) {a b : ℤ}
    (ha : a≤A) (hb : B≤b) (I : Schedule h m k ds s a b) : C≤b-a := by
  induction run generalizing a b with
  | done s A B => omega
  | small choose tail ih =>
    cases I with
    | small hp ht rest =>
      exact ih hm (by omega) (by omega) rest
    | large hp ht rest => omega
  | large choose tail ih => omega

/-- The stated factor two, including the all-small case, against every schedule. -/
theorem algorithm1_two_approximation {h C a b : ℤ} {m k : ℕ} {ds : List ℤ}
    (hh : 1≤h) (hd : ∀ d ∈ ds, 0≤d) (hlen : ds.length=m+k)
    (htotal : ds.sum=h*m) (run : Algorithm1Run h m k ds 0 0 0 C)
    (ha : a≤0) (hb : 0≤b) (I : Schedule h m k ds 0 a b) :
    C+1 ≤ 2*(b-a+1) := by
  by_cases hm : m=0
  · have valid : ValidPrefix h m k ds 0 0 0 :=
      ⟨hd,hlen,by simpa using htotal,le_rfl,le_rfl,le_rfl,le_rfl⟩
    have := run_no_large_le ((run_iff_algorithm1 hh valid).mpr run) hm ha hb I
    omega
  · have := algorithm1_ratio_bound hh (by omega) hd hlen htotal run ha hb I
    nlinarith

/-- The LP rule always has a run and its reported bound is attained by an
integral schedule, so the correspondence is not a vacuous implication. -/
theorem algorithm1_exists {h : ℤ} {m k : ℕ} {ds : List ℤ}
    (hh : 1≤h) (hd : ∀ d ∈ ds, 0≤d) (hlen : ds.length=m+k)
    (htotal : ds.sum=h*m) :
    ∃ C a b, Algorithm1Run h m k ds 0 0 0 C ∧
      a≤0 ∧ 0≤b ∧ Schedule h m k ds 0 a b ∧ b-a=C := by
  have valid : ValidPrefix h m k ds 0 0 0 :=
    ⟨hd,hlen,by simpa using htotal,le_rfl,le_rfl,le_rfl,le_rfl⟩
  obtain ⟨C,run⟩ := run_exists h ds m k 0 0 0 hlen
  obtain ⟨a,b,ha,hb,I,he⟩ := run_has_schedule run (by simpa using htotal)
  exact ⟨C,a,b,(run_iff_algorithm1 hh valid).mp run,ha,hb,I,he⟩

end Gasoline.Integer
