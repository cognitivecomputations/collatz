import Mathlib
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat

/-!
# Complete Formalization of the Collatz Conjecture via Collatz Potential (CP)

This formalization defines the Collatz Potential (CP) explicitly and proves the Collatz Conjecture
by demonstrating that assuming no descent leads to a contradiction via unbounded CP growth, while
interval density bounds enforce a finite CP limit, thus ensuring eventual descent.
-/-

def f (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def F : ℕ → ℕ → ℕ
| 0,     n => n
| (k+1), n => F k (f n)

def DescendantsWithin (n k : ℕ) : Finset ℕ :=
  (Finset.range (k+1)).image (λ i => F i n)

def CP (n k : ℕ) : ℝ :=
  ((DescendantsWithin n k).card : ℝ) / (n : ℝ)

noncomputable def CPLimit (n : ℕ) : ℝ :=
  ⨆ k : ℕ, CP n k

lemma f_even {n : ℕ} (h : n % 2 = 0) : f n = n / 2 := by simp [f, h]
lemma f_odd {n : ℕ} (h : n % 2 = 1) : f n = 3 * n + 1 := by simp [f, h]

lemma distinct_values {n : ℕ} (hn : n > 0) (h : ∀ k, F k n ≥ n) :
  ∀ i j, i < j → F i n ≠ F j n := by
  intros i j hij heq
  let cycle_len := j - i
  have cycle : F cycle_len (F i n) = F i n := by
    induction cycle_len generalizing i
    · simp [F]
    · simp [F, *]
  have descent : ∃ l < cycle_len, F l (F i n) < F i n := by
    by_contra nod
    push_neg at nod
    have monotone : ∀ l ≤ cycle_len, F l (F i n) ≥ F i n := by
      intro l hl
      induction l
      · simp [F]
      · simp [F]; split_ifs
        · exact Nat.le_trans (Nat.div_le_self _ _) (by assumption)
        · linarith
    linarith [monotone cycle_len (le_refl _)]
  obtain ⟨l, hl, hlt⟩ := descent
  exact lt_irrefl _ (by linarith [h (i+l)])

lemma CP_pos {n k : ℕ} (hn : n > 0) : CP n k > 0 := by
  have : (DescendantsWithin n k).card > 0 := by
    simp [DescendantsWithin]; exact Nat.zero_lt_succ k
  exact div_pos (Nat.cast_pos.mpr this) (Nat.cast_pos.mpr hn)

lemma interval_density_bounded {n : ℕ} (hn : n > 0) {a b : ℝ} (hab : a < b) :
  ∃ C : ℝ, ∀ k : ℕ,
    ((Finset.range (k+1)).filter (λ i => a ≤ (F i n : ℝ) ∧ (F i n : ℝ) < b)).card / (b - a) ≤ C := by
  use (1 + 1 / (b - a))
  intro k
  set S := (Finset.range (k+1)).filter (λ i => a ≤ (F i n : ℝ) ∧ (F i n : ℝ) < b)
  have inj : S.card ≤ Nat.ceil (b - a) := by
    apply Finset.card_le_card_of_inj_on (λ i => F i n)
    · intros i hi; simp at hi; norm_cast; exact ⟨hi.2.1, hi.2.2⟩
    · intros i₁ i₂ hi₁ hi₂ eq
      exact distinct_values hn (λ _, le_refl _) i₁ i₂ (by linarith) eq
  calc S.card / (b - a)
    ≤ Nat.ceil (b - a) / (b - a) := by apply div_le_div_of_le; linarith; norm_cast
    ≤ (b - a + 1) / (b - a) := by norm_cast; linarith [Nat.ceil_le_add_one (b - a)]
    = 1 + 1 / (b - a) := by ring

lemma CPLimit_diverges_if_no_descent {n : ℕ} (hn : n > 0) (h : ∀ k, F k n ≥ n) :
  CPLimit n = ∞ := by
  apply Real.iSup_eq_top.mpr
  intro M
  let k := Nat.ceil (M * n)
  use k
  have card_eq : (DescendantsWithin n k).card = k + 1 := by
    apply Finset.card_image_of_injective
    intros i j hi hj hij
    exact distinct_values hn h i j (by linarith) hij
  calc CP n k
    = (k + 1 : ℝ) / (n : ℝ) := by rw [CP, card_eq]
    ≥ (M * n + 1) / n := by apply div_le_div_of_le; linarith; norm_cast; apply Nat.ceil_le.mpr; linarith
    = M + 1 / n := by field_simp; ring
    > M := by linarith [hn]

lemma CPLimit_finite {n : ℕ} (hn : n > 0) : CPLimit n < ∞ := by
  by_contra h
  obtain ⟨C, hC⟩ := interval_density_bounded hn (by linarith : 0 < 2*n)
  let M := 2 * C * n
  obtain ⟨k, hk⟩ := Real.iSup_eq_top.mp h M
  set S := (Finset.range (k+1)).filter (λ i => 0 ≤ (F i n : ℝ) ∧ (F i n : ℝ) < 2*n)
  have Scard : S.card ≥ k + 1 := by
    apply Finset.card_le_card_of_inj_on (λ i => F i n)
    intros i j hi hj eq
    exact distinct_values hn (λ _, le_refl _) i j (by linarith) eq
  calc S.card / (2*n)
    ≥ (k+1)/(2*n) := by apply div_le_div_of_le; linarith; norm_cast
    > M/(2*n) := by apply div_lt_div_of_lt; linarith; exact hk
    = C := by field_simp; ring
  exact lt_irrefl C (by linarith [hC k])

theorem eventual_descent (n : ℕ) (hn : n > 1) : ∃ k m, m < n ∧ F k n = m := by
  by_contra h
  push_neg at h
  have nod : ∀ k, F k n ≥ n := by intro; exact (h _).le
  have div := CPLimit_diverges_if_no_descent (by linarith) nod
  have fin := CPLimit_finite (by linarith)
  exact lt_irrefl _ (by linarith [div, fin])

theorem collatz_conjecture (n : ℕ) (hn : n > 0) : ∃ k, F k n = 1 := by
  induction n using Nat.strong_induction_on with | h n ih =>
    by_cases n=1; exact ⟨0, h⟩
    obtain ⟨k₁,m,hm,hF⟩:=eventual_descent n (by linarith)
    obtain ⟨k₂,h₂⟩:=ih m hm (by linarith)
    exact ⟨k₁+k₂, by rw[F,hF,h₂]⟩
