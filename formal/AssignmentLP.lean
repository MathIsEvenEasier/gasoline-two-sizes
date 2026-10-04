import Assignment
import IntegerModel

set_option maxHeartbeats 2000000

namespace Gasoline
open Finset

/-- Weighted original deliveries are exactly 1+h times the large-item fraction. -/
lemma assignment_delivery {m k n : ℕ} (M : Assignment m k n) (h : ℝ) (j : Fin n) :
    (h+1) * (∑ i, M.large i j) + (∑ i, M.small i j) =
      1 + h * (∑ i, M.large i j) := by
  have := M.column j
  nlinarith

/-- The actual peak and trough inequalities for a specified vector of deliveries.
With offset 1 the deliveries are 1+z_j and the demands are 1+d_j.
The terminal equality enforces conservation of total supply. -/
def DeliveryTrace (offset : ℝ) : (ds : List ℝ) → (Fin ds.length → ℝ) →
    ℝ → ℝ → ℝ → Prop
  | [], _, s, _, _ => s = 0
  | d::ds, z, s, a, b => s+z 0+offset ≤ b ∧ a ≤ s+z 0-d ∧
      DeliveryTrace offset ds (fun j => z j.succ) (s+z 0-d) a b

lemma deliveryTrace_shift (offset : ℝ) (ds : List ℝ)
    (z : Fin ds.length → ℝ) (s a b : ℝ) :
    DeliveryTrace offset ds z s a (b+offset) ↔ DeliveryTrace 0 ds z s a b := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
    simp only [DeliveryTrace, add_le_add_iff_right, add_zero, ih]

lemma deliveryTrace_total (offset : ℝ) (ds : List ℝ)
    (z : Fin ds.length → ℝ) (s a b : ℝ)
    (ht : DeliveryTrace offset ds z s a b) : ∑ j, z j = ds.sum-s := by
  induction ds generalizing s with
  | nil => simp only [DeliveryTrace] at ht; simp [ht]
  | cons d ds ih =>
    rcases ht with ⟨_,_,tail⟩
    have total := ih (fun j => z j.succ) (s+z 0-d) tail
    change (∑ j : Fin (ds.length+1), z j) = (d::ds).sum-s
    rw [Fin.sum_univ_succ]
    simp only [List.sum_cons]
    linarith

lemma reach_iff_deliveryTrace (h : ℝ) (ds : List ℝ) (s a b : ℝ) :
    Reach h ds s a b ↔ ∃ z : Fin ds.length → ℝ,
      (∀ j, 0 ≤ z j ∧ z j ≤ h) ∧ DeliveryTrace 0 ds z s a b := by
  induction ds generalizing s with
  | nil =>
    simp only [Reach, DeliveryTrace]
    constructor
    · intro hs; exact ⟨Fin.elim0,by intro j; exact Fin.elim0 j,hs⟩
    · rintro ⟨_,_,hs⟩; exact hs
  | cons d ds ih =>
    constructor
    · rintro ⟨q,hq0,hqh,hp,ht,tail⟩
      obtain ⟨z,hz,htrace⟩ := (ih (s+q-d)).mp tail
      refine ⟨Fin.cons q z,?_,?_⟩
      · intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simpa using And.intro hq0 hqh
        · simpa using hz k
      · simpa only [DeliveryTrace,Fin.cons_zero,Fin.cons_succ,add_zero] using
          And.intro hp (And.intro ht htrace)
    · rintro ⟨z,hz,hp,ht,tail⟩
      refine ⟨z 0,(hz 0).1,(hz 0).2,by simpa using hp,ht,?_⟩
      exact (ih (s+z 0-d)).mpr ⟨fun j => z j.succ,fun j => hz j.succ,tail⟩

/-- The residual assignment LP in original positive-size units. Its variables
are a genuine nonnegative doubly stochastic assignment and the inventory bounds.
No closed-form score or optimum is built into this feasible-set definition.
The normalized prefix extrema A,B correspond to original extrema A,B+1. -/
def MatrixBand (h : ℝ) (m k : ℕ) (ds : List ℝ) (s A B a b : ℝ) : Prop :=
  a ≤ A ∧ B+1 ≤ b ∧ ∃ M : Assignment m k ds.length,
    DeliveryTrace 1 ds (fun j => h * ∑ i, M.large i j) s a b

/-- Elimination of the assignment matrix, including the exact supply counts. -/
theorem matrixBand_iff_band {h : ℝ} (hh : 0 < h) (m k : ℕ)
    (ds : List ℝ) (hlen : ds.length = m+k) (s A B a b : ℝ)
    (htotal : ds.sum-s = h*(m:ℝ)) :
    MatrixBand h m k ds s A B a (b+1) ↔ Band h ds s A B a b := by
  constructor
  · rintro ⟨ha,hb,M,ht⟩
    have bounds := (assignment_to_fraction M).1
    refine ⟨ha,by linarith,(reach_iff_deliveryTrace h ds s a b).mpr ?_⟩
    refine ⟨fun j => h * ∑ i, M.large i j,?_,(deliveryTrace_shift 1 ds _ s a b).mp ht⟩
    intro j
    constructor
    · exact mul_nonneg hh.le (bounds j).1
    · have := mul_le_mul_of_nonneg_left (bounds j).2 hh.le
      simpa using this
  · rintro ⟨ha,hb,hr⟩
    obtain ⟨z,hz,ht⟩ := (reach_iff_deliveryTrace h ds s a b).mp hr
    have hsum : ∑ j, z j / h = (m:ℝ) := by
      rw [← sum_div,deliveryTrace_total 0 ds z s a b ht,htotal]
      field_simp
    have hp : ∀ j, 0 ≤ z j / h ∧ z j / h ≤ 1 := by
      intro j
      exact ⟨div_nonneg (hz j).1 hh.le,(div_le_one hh).mpr (hz j).2⟩
    obtain ⟨M,hM⟩ := fraction_to_assignment m k ds.length hlen (fun j => z j/h) hp hsum
    have hzM : (fun j => h * ∑ i, M.large i j) = z := by
      funext j
      rw [hM j]
      field_simp
    refine ⟨ha,by linarith,M,?_⟩
    rw [hzM]
    exact (deliveryTrace_shift 1 ds z s a b).mpr ht

/-- An attained minimum of the actual assignment LP objective beta-alpha. -/
def LPValue (h : ℝ) (m k : ℕ) (ds : List ℝ) (s A B v : ℝ) : Prop :=
  (∃ a b, MatrixBand h m k ds s A B a b ∧ b-a=v) ∧
  (∀ a b, MatrixBand h m k ds s A B a b → v ≤ b-a)

lemma LPValue.unique {h : ℝ} {m k : ℕ} {ds : List ℝ} {s A B v w : ℝ}
    (hv : LPValue h m k ds s A B v) (hw : LPValue h m k ds s A B w) : v=w := by
  obtain ⟨a,b,hb,he⟩ := hv.1
  obtain ⟨a',b',hb',he'⟩ := hw.1
  have := hv.2 a' b' hb'
  have := hw.2 a b hb
  linarith

/-- The independently defined assignment LP has the closed-form optimum +1. -/
theorem matrixLP_value {h : ℝ} (hh : 0 < h) (m k : ℕ) (ds : List ℝ)
    (hd : ∀ d ∈ ds, 0 ≤ d) (hlen : ds.length=m+k) (s A B : ℝ)
    (htotal : ds.sum-s=h*m) (hA : A≤0) (hB : 0≤B) (hAs : A≤s) (hsB : s≤B) :
    LPValue h m k ds s A B (prefixValue h ds s A B+1) := by
  have he0 : 0 ≤ ds.sum-s := by rw [htotal]; positivity
  have hbudget : budget h ds = h * ds.length := by
    suffices ∀ es : List ℝ, budget h es = h * es.length from this ds
    intro es
    induction es with
    | nil => simp [budget]
    | cons d ds ih => simp [budget,ih]; ring
  have heN : ds.sum-s ≤ budget h ds := by
    rw [htotal,hbudget,hlen,Nat.cast_add]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  constructor
  · obtain ⟨a,b,hband,he⟩ := prefix_attained hh.le ds hd s A B hA hB hAs hsB he0 heN
    exact ⟨a,b+1,(matrixBand_iff_band hh m k ds hlen s A B a b htotal).mpr hband,by linarith⟩
  · intro a b hband
    have hm : MatrixBand h m k ds s A B a ((b-1)+1) := by simpa using hband
    have hn := (matrixBand_iff_band hh m k ds hlen s A B a (b-1) htotal).mp hm
    have := prefix_lower hh.le ds hd s A B a (b-1) hA hB hAs hsB hn
    linarith

end Gasoline
