import Mathlib.Tactic

namespace Gasoline
open Finset

/-- The unfixed assignment matrix, with its rows grouped by supply size. -/
structure Assignment (m l n : ℕ) where
  large : Fin m → Fin n → ℝ
  small : Fin l → Fin n → ℝ
  large_nonneg : ∀ i j, 0 ≤ large i j
  small_nonneg : ∀ i j, 0 ≤ small i j
  large_row : ∀ i, ∑ j, large i j = 1
  small_row : ∀ i, ∑ j, small i j = 1
  column : ∀ j, (∑ i, large i j) + (∑ i, small i j) = 1

theorem assignment_to_fraction {m l n : ℕ} (M : Assignment m l n) :
    (∀ j, 0 ≤ ∑ i, M.large i j ∧ (∑ i, M.large i j) ≤ 1) ∧
    (∑ j, ∑ i, M.large i j) = (m : ℝ) := by
  constructor
  · intro j
    have hl : 0 ≤ ∑ i, M.large i j := sum_nonneg (by intro i _; exact M.large_nonneg i j)
    have hs : 0 ≤ ∑ i, M.small i j := sum_nonneg (by intro i _; exact M.small_nonneg i j)
    exact ⟨hl,by have := M.column j; linarith⟩
  · rw [sum_comm]
    simp [M.large_row]

/-- Every bounded fractional supply vector with the right total is realized by
an actual doubly stochastic assignment matrix, including empty supply classes. -/
theorem fraction_to_assignment (m l n : ℕ) (hn : n = m+l)
    (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hsum : ∑ j, p j = (m : ℝ)) :
    ∃ M : Assignment m l n, ∀ j, (∑ i, M.large i j) = p j := by
  have hres : ∑ j, (1-p j) = (l : ℝ) := by
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsum]
    have hc : (n : ℝ) = (m : ℝ)+(l : ℝ) := by exact_mod_cast hn
    linarith
  have pzero (hm : m=0) (j : Fin n) : p j = 0 := by
    have hle : p j ≤ ∑ k, p k := single_le_sum (fun k _ => (hp k).1) (mem_univ j)
    rw [hsum,hm] at hle
    have := (hp j).1
    norm_num at hle
    linarith
  have pone (hl : l=0) (j : Fin n) : p j = 1 := by
    have hle : 1-p j ≤ ∑ k, (1-p k) := single_le_sum (f := fun k => 1-p k) (fun k _ => by have := (hp k).2; linarith) (mem_univ j)
    rw [hres,hl] at hle
    have := (hp j).2
    norm_num at hle
    linarith
  have large_col (j : Fin n) : (∑ _i : Fin m, p j / (m : ℝ)) = p j := by
    by_cases hm : m=0
    · simp [hm,pzero hm j]
    · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
  have small_col (j : Fin n) : (∑ _i : Fin l, (1-p j) / (l : ℝ)) = 1-p j := by
    by_cases hl : l=0
    · simp [hl,pone hl j]
    · have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
  let M : Assignment m l n := {
    large := fun _ j => p j / m
    small := fun _ j => (1-p j) / l
    large_nonneg := fun _ j => div_nonneg (hp j).1 (Nat.cast_nonneg m)
    small_nonneg := fun _ j => div_nonneg (by have := (hp j).2; linarith) (Nat.cast_nonneg l)
    large_row := by
      intro i
      have hm : m ≠ 0 := by have := i.isLt; omega
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      rw [← sum_div,hsum,div_self hmR]
    small_row := by
      intro i
      have hl : l ≠ 0 := by have := i.isLt; omega
      have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl
      rw [← sum_div,hres,div_self hlR]
    column := by intro j; rw [large_col j,small_col j]; ring }
  exact ⟨M,large_col⟩

#print axioms Gasoline.assignment_to_fraction
#print axioms Gasoline.fraction_to_assignment
end Gasoline
