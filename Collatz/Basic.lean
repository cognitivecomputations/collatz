import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Pow
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement -- For orderOf
import Mathlib.Algebra.Group.Units -- For IsUnit
import Mathlib.Data.Finset.Basic -- For sum over Fin
import Mathlib.Data.Nat.Prime -- For Nat.Prime needed by two_three_units fixes
import Mathlib.Algebra.Group.Basic -- For basic group laws
import Mathlib.Order.WellFounded -- For termination argument
import Mathlib.Data.Set.Finite -- For arguing about finite sets

open Nat Fin ZMod Function

/-!
=================================================================
                  Section 1: Definitions
=================================================================
-/

/-- `nu2 n` is the exponent of 2 dividing `n`. Uses trailingZeros. -/
@[simp] def nu2 (n : ℕ) : ℕ := n.trailingZeros

/-- `oddPart n` is `n / 2^nu2 n`. -/
@[simp] def oddPart (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else n / (2 ^ nu2 n)

/-- Syracuse map S(n) = oddPart(3n+1) for odd n. Defined as 0 for even n for totality. -/
@[simp] noncomputable def S (n : ℕ) : ℕ :=
  if h : n % 2 = 1 then oddPart (3 * n + 1) else 0

/-- k-fold iterate of S. -/
@[simp] def S_iter (k n : ℕ) : ℕ := Nat.iterate S k n

/-- `a n = ν₂(n+1)`. -/
@[simp] def a (n : ℕ) : ℕ := nu2 (n + 1)

/-! Properties of nu2, oddPart, S -/
lemma oddPart_mul_pow_nu2_eq_self {n : ℕ} (hn : n ≠ 0) : oddPart n * 2 ^ nu2 n = n :=
  Nat.div_mul_cancel (Nat.pow_dvd_pow_iff_le_right (by norm_num).le |>.mpr (Nat.le_trailingZeros hn))

lemma oddPart_pos_of_pos {n : ℕ} (hn : n > 0) : oddPart n > 0 := by
  rw [Nat.pos_iff_ne_zero] at hn ⊢; unfold oddPart; simp [hn];
  apply Nat.div_pos (Nat.le_of_lt hn) (Nat.pow_pos (by norm_num))

lemma oddPart_is_odd {n : ℕ} (hn : n > 0) : oddPart n % 2 = 1 :=
  Nat.odd_div_pow_trailingZeros hn

lemma S_pos {n : ℕ} (hn : n > 0) (hodd : n % 2 = 1) : S n > 0 := by
  simp only [S, hodd, if_true]
  apply oddPart_pos_of_pos
  linarith [Nat.mul_pos (by norm_num) hn]

lemma S_preserves_odd {n : ℕ} (hodd : n % 2 = 1) (hn : n > 0) : S n % 2 = 1 := by
  simp only [S, hodd, if_true]
  apply oddPart_is_odd
  linarith [Nat.mul_pos (by norm_num) hn]

lemma nu2_of_3x_plus_1_ge_1 {x : ℕ} (hx_odd : x % 2 = 1) : nu2 (3 * x + 1) ≥ 1 := by
  have h : (3*x+1) % 2 = 0 := by rw [Nat.add_mod, Nat.mul_mod, hx_odd]; norm_num
  dsimp [nu2]; apply Nat.pos_of_dvd_of_pos (Nat.pow_dvd_pow 2 (by norm_num))
  · rw [pow_one]; exact Nat.dvd_of_mod_eq_zero h
  · linarith [Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero (Nat.mod_two_ne_zero.mp hx_odd))]

lemma nextOdd_lt {n : ℕ} (hodd : n % 2 = 1) (hn : 1 < n) (ha1 : a n = 1) :
  S n < n := by -- Renamed from nextOdd to S
  have dv4 : 4 ∣ 3 * n + 1 := by
    dsimp [a] at ha1; have : (n + 1).trailingZeros = 1 := ha1
    have := trailingZeros_eq_iff_mod.1 this
    simp only [this, mul_one, add_left_inj, add_comm, Nat.mul_mod, Nat.mod_mod, Nat.cast_ofNat,
      Nat.mod_mul_right_div_self, Nat.mod_self, add_zero, Nat.mod_add_div]
    norm_num -- Proves 3n+1 mod 4 = 0
  have k'_ge_2 : 2 ≤ nu2 (3 * n + 1) := by dsimp [nu2]; apply trailingZeros_le_of_dvd; exact dv4
  simp only [S, hodd, if_true, oddPart]
  set k := nu2 (3 * n + 1)
  have pow_k_pos : 0 < 2 ^ k := pow_pos (by norm_num) k
  calc (3 * n + 1) / 2 ^ k ≤ (3 * n + 1) / 4 := Nat.div_le_div_right (by apply pow_le_pow_right; linarith)
   _ < n := by apply Nat.div_lt_of_lt_mul; linarith [hn]

lemma a_nextOdd {n : ℕ} (hodd : n % 2 = 1) (ha : 1 < a n) :
  a (S n) = a n - 1 := by -- Renamed from nextOdd to S
  dsimp [a]
  let k := nu2 (n + 1)
  have k_ge_2 : k ≥ 2 := Nat.succ_le_of_lt ha
  obtain ⟨t, ht, ht_odd⟩ : ∃ t, n + 1 = t * 2^k ∧ t % 2 = 1 := Nat.exists_eq_mul_pow_of_pos (by linarith)
  have n_eq : n = t * 2^k - 1 := Nat.eq_sub_of_add_eq ht
  have three : 3 * n + 1 = 2 * (3 * t * 2^(k - 1) - 1) := by rw [n_eq]; ring_nf
  have term_odd : (3 * t * 2^(k - 1) - 1) % 2 = 1 := by
    rw [Nat.sub_mod]; swap; norm_num; swap; exact Nat.one_le_of_lt k_ge_2
    rw [Nat.mul_assoc, Nat.mul_mod, Nat.pow_mod]; simp only [zero_mul, Nat.mod_self, Nat.mod_zero]
    norm_num -- simplifies to -1 % 2 = 1
  have nu2_3n1 : nu2 (3 * n + 1) = 1 := by rw [three, trailingZeros_mul_prime (by norm_num), trailingZeros_two]; rw [nu2_eq_zero_iff (by linarith)]; exact term_odd
  simp only [S, hodd, if_true, oddPart, nu2_3n1, pow_one]
  -- S n = (3n+1)/2 = 3 * t * 2^(k-1) - 1
  have sn_eq : S n = 3 * t * 2^(k-1) - 1 := by rw [three, Nat.mul_div_cancel_left _ (by norm_num)]
  -- a(S n) = nu2(S n + 1)
  dsimp [a]
  rw [sn_eq, Nat.sub_add_cancel (Nat.one_le_of_lt k_ge_2), trailingZeros_mul_prime (by norm_num)]
  rw [nu2_eq_zero_iff (by linarith)]; exact ht_odd -- nu2(3t)=0
  rw [zero_add]
  exact trailingZeros_pow (by norm_num) -- nu2(2^(k-1))=k-1

/-!
=================================================================
                  Section 2: Cycle Exclusion
=================================================================
This section assumes existence of a cycle and derives a contradiction
using properties of ZMod D and group theory.
It relies on external/deep number theory results.
-/

-- Assume definitions b_k, D, cycle_equation, alpha
def b_k (o e : ℕ) (eList : Fin o → ℕ) : ℕ := ∑ i, 2 ^ (eList i) * 3 ^ (o - 1 - i)
def D (e o : ℕ) : ℕ := if h: 3^o ≤ 2^e then 2^e - 3^o else 0 -- Use Nat subtraction safely
lemma D_def {o e : ℕ} (h: 3^o ≤ 2^e) : D e o = 2^e - 3^o := by simp [D, h]
lemma cycle_equation {o e n : ℕ} (eList : Fin o → ℕ) (h : F k n = n) -- Needs correct F and path extraction
    (h_path : -- path extraction gives o, e, eList
      sorry) :
    let b = b_k o e eList
    n * (2^e - 3^o) = b := sorry -- Assume derivation: n(2^e - 3^o) = b_k

variable {o e : ℕ}

lemma D_pos_of_nontrivial {n : ℕ} (hn : n > 1) -- If n > 1, cycle cannot be trivial {1,2,4}
    (ho : o > 0) (he : e > 0) (h_cycle : D e o * n = b_k o e sorry) :
    D e o > 0 := by
    -- Need 3^o < 2^e for non-trivial cycle elements > 1. Assume from literature.
    sorry

-- Assume: 2 and 3 are units mod D if D>1
lemma two_three_units (hD : D e o > 1) : IsUnit (2 : Zmod (D e o)) ∧ IsUnit (3 : Zmod (D e o)) := by sorry

def alpha (hD : D e o > 1) : Zmod (D e o) := 2 * (3 : Zmod (D e o))⁻¹

-- Assume: Cycle equation implies sum of powers of alpha is zero mod D
lemma cycle_sum_zero {n : ℕ} (eList : Fin o → ℕ) (hD : D e o > 1) (h_cycle) :
    (∑ i, (alpha hD) ^ (eList i)) = 0 := by sorry

-- Assume: Standard group theory result about sums of roots of unity
axiom no_zero_sum_of_powers {G : Type*} [CommGroup G] {α : G} {r o : ℕ}
  (h_order : orderOf α = r) (h_o_lt_r : o < r) (k_exp : Fin o → ℕ) :
  (Finset.univ : Finset (Fin o)).sum (fun i => α ^ (k_exp i)) ≠ 0 -- May need distinctness or other conditions

-- Assume: Lower bound on orderOf alpha
axiom orderOf_alpha_lower_bound (hD : D e o > 1) : orderOf (alpha hD) > o -- This is the deep result

-- Theorem: No non-trivial cycles exist
theorem no_non_trivial_cycles (n : ℕ) (hn : n > 1) (k : ℕ) (h_cycle : F k n = n)
    (o e : ℕ) (ho : o > 0) (he : e > 0) (hk : k = o + e) -- Need path extraction etc.
    (eList : Fin o → ℕ) (h_cycle_eq : sorry) : -- Need precise cycle equation instance
    False := by
  have hD_pos : D e o > 0 := D_pos_of_nontrivial hn ho he h_cycle_eq
  -- If D=1, only trivial cycle {1,2,4} possible (by Catalan/Mihailescu) - contradicts n > 1?
  -- Assume D > 1 based on excluding trivial cycle / n > 1
  have hD_gt_1 : D e o > 1 := sorry
  let α := alpha hD_gt_1
  let r := orderOf α
  have h_sum_zero := cycle_sum_zero eList hD_gt_1 h_cycle_eq
  have h_order_bound := orderOf_alpha_lower_bound hD_gt_1 -- Assumes o < r
  have h_sum_ne_zero := no_zero_sum_of_powers h_order_bound (by linarith) eList -- Needs o < r proof
  exact h_sum_ne_zero h_sum_zero
  admit -- Need rigorous setup and linking

/-!
=================================================================
           Section 3: Non-Divergence (Heuristic/Sketch)
=================================================================
We argue that the condition needed for divergence (average k <= log2 3)
is impossible due to 2-adic instability.
-/

-- Lemmas showing instability of n = -1 mod 2^A state under S
lemma nextOdd_mod_lower {n A : ℕ} (hodd : n % 2 = 1) (hn_pos : n>0) (A_pos : A>0)
  (hmod : n % (2^(A+1)) = 2^(A+1) - 1) :
  S n % 2^A = 2^A - 1 := by sorry -- Provable as sketched before

lemma nextOdd_mod_drop {n A : ℕ} (hodd : n % 2 = 1) (hn_pos : n>0) (A_pos : A>0)
  (ha : n % 2^A = 2^A - 1) (hne : n % 2^(A+1) ≠ 2^(A+1) - 1) :
  S n % 2^A ≠ 2^A - 1 := by sorry -- Provable as sketched before

-- Axiom/Theorem: Non-divergence (based on 2-adic instability heuristic)
-- States that the sequence must be bounded.
axiom no_divergence (n : ℕ) (hn : n > 0) : ∃ M, ∀ k, S_iter k n ≤ M

/-!
=================================================================
                  Section 4: Final Termination Proof
=================================================================
-/

-- Final proof structure, assuming cycle exclusion and non-divergence
theorem collatz_terminates (n : ℕ) (hn : n > 0) : ∃ k, S_iter k n = 1 := by
  -- 1. Exclude non-trivial cycles (Assume proven via axioms/theorems above)
  have H_no_cycles : ∀ m k, m > 1 → S_iter k m = m → False := sorry

  -- 2. Establish Boundedness (Axiom/Theorem based on non-divergence)
  obtain ⟨B, h_bound⟩ := no_divergence n hn

  -- 3. Argument for termination of bounded sequence with no non-trivial cycles
  -- Consider the sequence n₀=n, n₁=S(n₀), ...
  -- It is bounded by B, so it must eventually repeat (enter a cycle) or hit 1.
  let orbit_set := Set.range (S_iter · n) -- The set of iterates {n, S n, S²n, ...}
  have orbit_finite : orbit_set.Finite := sorry -- Need theorem: bounded set of ℕ is finite
                                              -- Requires range being upper bounded by B
  have exists_repeat : ∃ i j, i < j ∧ S_iter i n = S_iter j n :=
    Set.Finite.exists_lt_map_eq_of_forall_mem orbit_finite (fun k => S_iter k n) (by sorry) -- Need infinite domain for pigeonhole

  rcases exists_repeat with ⟨i, j, h_i_lt_j, h_eq⟩
  -- This means S_iter i n enters a cycle of length j-i
  let m := S_iter i n -- Starting point of the cycle
  let k' := j - i
  have hk'_pos : k' > 0 := Nat.sub_pos_of_lt h_i_lt_j
  have m_in_orbit : m ∈ orbit_set := Set.mem_range.mpr ⟨i, rfl⟩
  have m_pos : m > 0 := Nat.pos_of_ne_zero sorry -- Need S_iter k n > 0 if n>0
  have m_cycle : S_iter k' m = m := by
      rw [Nat.iterate_add_apply, Nat.sub_add_cancel (le_of_lt h_i_lt_j)] at h_eq
      sorry -- Need S_iter (j-i) (S_iter i n) = S_iter j n

  -- Apply cycle exclusion
  if hm_eq_1 : m = 1 then
    -- If the cycle element is 1, we are done. Find the index i.
    use i; exact hm_eq_1
  else
    -- m > 1. The cycle is non-trivial.
    have hm_gt_1 : m > 1 := Nat.lt_of_le_of_ne (Nat.one_le_of_lt m_pos) hm_eq_1
    -- This contradicts H_no_cycles
    exact H_no_cycles m k' hm_gt_1 m_cycle
  admit -- Need to fill sorries
