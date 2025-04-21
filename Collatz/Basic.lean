import Mathlib.Data.Nat.Basic          -- Basic Nat definitions and theorems
import Mathlib.Tactic.Linarith         -- For linear arithmetic proofs
import Mathlib.Data.Nat.Pow           -- For powers
import Mathlib.Data.Nat.Prime         -- For Nat.Prime definition (used in units proof)
import Mathlib.Data.Nat.Factorization.Basic -- For multiplicity/trailingZeros
import Mathlib.Data.ZMod.Basic          -- For ZMod M
import Mathlib.Algebra.Group.Units       -- For IsUnit
import Mathlib.GroupTheory.OrderOfElement -- For orderOf
import Mathlib.Algebra.GroupPower.Basic   -- For pow properties
import Mathlib.Order.WellFounded       -- For termination arguments
import Mathlib.Data.Set.Finite           -- For finite sets in termination
import Mathlib.Init.Data.Nat.Lemmas   -- For basic Nat lemmas like one_le_of_lt

open Nat Fin ZMod Function

/-!
=================================================================
                  Section 1: Definitions and Basic Properties
=================================================================

We define the core functions and prove basic properties relating to
the Syracuse map S (also called nextOdd), which maps an odd integer n
to the next odd integer in its Collatz sequence, and the function
a(n) = ν₂(n+1).
-/

/-- `nu2 n` is the exponent of 2 dividing `n`. Uses trailingZeros. -/
@[simp] noncomputable def nu2 (n : ℕ) : ℕ :=
  -- Handle n=0 explicitly for multiplicity.get
  if h : n = 0 then 0 else (multiplicity 2 n).get (multiplicity_finite_of_ne_zero (by decide) h)

lemma nu2_eq_trailingZeros (n : ℕ) : nu2 n = n.trailingZeros := by
  unfold nu2; split_ifs with h
  · rw [h, Nat.trailingZeros_zero]
  · rw [Nat.multiplicity_two_eq_trailingZeros]

/-- `oddPart n` is `n / 2^nu2 n`. -/
@[simp] noncomputable def oddPart (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else n / (2 ^ nu2 n)

lemma oddPart_mul_pow_nu2_eq_self {n : ℕ} (hn : n ≠ 0) : oddPart n * 2 ^ nu2 n = n := by
  simp only [oddPart, hn, if_false]
  rw [nu2_eq_trailingZeros]
  exact Nat.div_mul_cancel (Nat.pow_trailingZeros_dvd hn)

lemma oddPart_pos_of_pos {n : ℕ} (hn : n > 0) : oddPart n > 0 := by
  rw [Nat.pos_iff_ne_zero] at hn ⊢; unfold oddPart; simp [hn]
  apply Nat.div_pos (Nat.le_of_lt hn) (Nat.pow_pos (by norm_num))

lemma oddPart_is_odd {n : ℕ} (hn : n > 0) : oddPart n % 2 = 1 := by
  rw [Nat.pos_iff_ne_zero] at hn
  apply Nat.odd_div_pow_trailingZeros hn

/-- `a n = ν₂(n+1)`. -/
@[simp] def a (n : ℕ) : ℕ := nu2 (n + 1)

/-- Syracuse map S(n) = oddPart(3n+1) for odd n. Returns 0 for even n. -/
@[simp] noncomputable def S (n : ℕ) : ℕ :=
  if h : n % 2 = 1 then oddPart (3 * n + 1) else 0

/-- k-fold iterate of S. Requires proof that input remains odd if started odd > 1. -/
@[simp] noncomputable def S_iter (k n : ℕ) : ℕ :=
  Nat.iterate S k n

-- We need positivity and oddness preservation to properly define iteration on relevant domain
lemma S_pos {n : ℕ} (hn : n > 0) (hodd : n % 2 = 1) : S n > 0 := by
  simp only [S, hodd, if_true]
  apply oddPart_pos_of_pos
  apply Nat.add_pos_left (Nat.mul_pos (by norm_num) hn) (by norm_num)

lemma S_preserves_odd {n : ℕ} (hodd : n % 2 = 1) (hn : n > 0) : S n % 2 = 1 := by
  simp only [S, hodd, if_true]
  apply oddPart_is_odd
  apply Nat.add_pos_left (Nat.mul_pos (by norm_num) hn) (by norm_num)

-- Helper function for iterating S on odd numbers > 1
-- Ensures the input to S is always appropriate
@[simp] noncomputable def S_iter_odd (k n : ℕ) (hodd : n % 2 = 1) (hn : n > 1) : { m // m % 2 = 1 ∧ m > 0 } :=
  match k with
  | 0 => ⟨n, And.intro hodd (lt_trans Nat.one_pos hn)⟩
  | k' + 1 =>
    let prev := S_iter_odd k' n hodd hn
    let m := S prev.val
    have m_odd : m % 2 = 1 := S_preserves_odd prev.property.1 prev.property.2
    have m_pos : m > 0 := S_pos prev.val prev.property.2 prev.property.1
    ⟨m, And.intro m_odd m_pos⟩

-- The result of S_iter_odd is the same as S_iter
lemma S_iter_odd_val (k n : ℕ) (hodd : n % 2 = 1) (hn : n > 1) :
    (S_iter_odd k n hodd hn).val = S_iter k n := by
  induction k generalizing n hodd hn with
  | zero => simp [S_iter_odd]
  | succ k ih =>
      simp only [S_iter_odd, Nat.iterate_succ_apply']
      let prev := S_iter_odd k n hodd hn
      -- Need to show S prev.val = S (Nat.iterate S k n)
      rw [← ih prev.val prev.property.1 (lt_trans Nat.one_pos prev.property.2)]
      admit -- requires showing prev.val > 1? Not necessarily if it hit 1. Needs care.


/-!
Section 1b: Key Lemmas on Dynamics of S and a(n)
-/

/-- Lemma 1: If `a n = 1` (so `n ≡ 1 [mod 4]`) and `n > 1`, then `S n < n`. -/
lemma S_lt_of_a_eq_1 {n : ℕ} (hodd : n % 2 = 1) (hn : 1 < n) (ha1 : a n = 1) :
  S n < n := by
  have n_pos : n > 0 := lt_trans Nat.one_pos hn
  have n1_pos : n + 1 > 0 := succ_pos n
  have a_rw : (n + 1).trailingZeros = 1 := by simpa [a, nu2_eq_trailingZeros] using ha1
  have mod4 : n % 4 = 1 := Nat.trailingZeros_eq_one_iff_mod_four_eq_two.mp a_rw ▸ rfl -- Need Nat lemma: tz=1 <=> n+1=2*(odd) <=> n+1=2[4] <=> n=1[4]
  have y_eq_3n1 : 3 * n + 1 > 0 := Nat.add_pos_left (Nat.mul_pos (by norm_num) n_pos) (by norm_num)
  have dv4 : 4 ∣ 3 * n + 1 := by
    rw [show n % 4 = 1 from mod4, ← Nat.dvd_iff_mod_eq_zero]
    apply Nat.dvd_of_mod_eq_zero
    simp only [Nat.mul_add_mod, Nat.mul_mod]
    norm_num -- 3*1+1 = 4; 4%4 = 0
  have k'_ge_2 : 2 ≤ nu2 (3 * n + 1) := by dsimp [nu2]; rw [nu2_eq_trailingZeros]; apply trailingZeros_le_of_dvd; exact dv4
  simp only [S, hodd, if_true, oddPart]
  set k := nu2 (3 * n + 1)
  have pow_k_pos : 0 < 2 ^ k := pow_pos (by norm_num) k
  calc (3 * n + 1) / 2 ^ k ≤ (3 * n + 1) / 4 := Nat.div_le_div_right (pow_le_pow_right (by norm_num) k'_ge_2)
     _ < n := by apply Nat.div_lt_of_lt_mul; linarith [hn] -- Needs 4 > 0
  admit -- Polish proof, fix lemma dependencies

/-- Lemma 2: If `a n > 1` then `a (S n) = a n - 1`. -/
lemma a_S_eq_a_sub_1 {n : ℕ} (hodd : n % 2 = 1) (hn_pos : n > 0) (ha_gt_1 : 1 < a n) :
  a (S n) = a n - 1 := by
  dsimp [a] -- Need ν₂(S n + 1) = ν₂(n + 1) - 1
  let k := nu2 (n + 1)
  have k_ge_2 : k ≥ 2 := Nat.succ_le_of_lt ha_gt_1
  have n1_pos : n+1 > 0 := succ_pos n
  obtain ⟨t, ht_eq, ht_odd⟩ : ∃ t, n + 1 = t * 2^k ∧ t % 2 = 1 :=
    Nat.exists_eq_mul_pow_of_pos n1_pos ▸ (nu2_eq_trailingZeros (n+1) ▸ Nat.trailingZeros_eq_iff_eq_mul_odd_pow).mp rfl
  have n_eq : n = t * 2^k - 1 := Nat.eq_sub_of_add_eq ht_eq
  have y_eq_3n1 : 3 * n + 1 = 2 * (3 * t * 2^(k - 1) - 1) := by rw [n_eq]; ring_nf
  have y_pos : 3*n+1 > 0 := Nat.add_pos_left (Nat.mul_pos (by norm_num) hn_pos) (by norm_num)
  have term_odd : (3 * t * 2^(k - 1) - 1) % 2 = 1 := by
    rw [Nat.sub_mod (Nat.one_le_of_lt k_ge_2)]
    rw [Nat.mul_assoc, Nat.mul_mod, Nat.pow_mod]; simp only [zero_mul, Nat.mod_self, Nat.mod_zero]
    norm_num -- 0 - 1 = -1; -1 % 2 = 1
  have nu2_y : nu2 (3 * n + 1) = 1 := by
    rw [y_eq_3n1, nu2_eq_trailingZeros, trailingZeros_mul_prime (by norm_num)]
    rw [nu2_eq_trailingZeros, trailingZeros_eq_zero_iff_odd.mpr term_odd]
    rw [zero_add, trailingZeros_two]
  simp only [S, hodd, if_true, oddPart, nu2_y, pow_one]
  -- S n = (3n+1)/2 = 3 * t * 2^(k-1) - 1
  have sn_eq : S n = 3 * t * 2^(k-1) - 1 := by rw [y_eq_3n1, Nat.mul_div_cancel_left _ (by norm_num)]
  -- a(S n) = nu2(S n + 1)
  rw [sn_eq, Nat.sub_add_cancel (Nat.one_le_mul_of_pos_of_pos (by norm_num) (Nat.pow_pos (by norm_num) _))] -- Need 3*t*2^(k-1) >= 1
  rw [nu2_eq_trailingZeros, trailingZeros_mul_prime (by norm_num)]
  rw [nu2_eq_trailingZeros, trailingZeros_eq_zero_iff_odd.mpr ht_odd, zero_add] -- nu2(3t)=0
  rw [trailingZeros_pow (by norm_num)] -- nu2(2^(k-1)) = k-1
  -- Result is k-1. Need to show this equals a n - 1 = nu2(n+1)-1.
  rw [show k = nu2 (n+1) by rw [nu2_eq_trailingZeros]]
  apply Nat.le_of_lt k_ge_2 -- Need 3*t*2^(k-1) >= 1
  admit -- Polish proof

/-!
=================================================================
                  Section 2: Cycle Exclusion (Axiomatic)
=================================================================
This section relies on deep results assumed as axioms.
-/

-- Axiom 1: No non-trivial cycles exist for the Syracuse map S.
axiom no_non_trivial_S_cycles (m : ℕ) (k : ℕ) : m > 1 → S_iter k m = m → k > 0 → False

/-!
=================================================================
                  Section 3: Non-Divergence (Axiomatic)
=================================================================
This relies on the 2-adic instability argument sketched previously,
which needs rigorous proof connecting it fully to boundedness.
-/

-- Axiom 2: Every Syracuse orbit is bounded.
axiom no_divergence (n : ℕ) (hn : n > 0) : ∃ B : ℕ, ∀ k : ℕ, S_iter k n ≤ B

/-!
=================================================================
                  Section 4: Final Termination Proof
=================================================================
-/

-- Helper: Iterates of S remain positive and odd if started odd > 1
lemma S_iter_odd_pos {n : ℕ} (hodd : n % 2 = 1) (hn : n > 0) (k : ℕ) :
    (S_iter k n) % 2 = 1 ∧ S_iter k n > 0 := by
  induction k generalizing n hodd hn with
  | zero => simp [S_iter]; exact ⟨hodd, hn⟩
  | succ k ih =>
    let prev_n := S_iter k n
    have h_prev := ih prev_n sorry sorry -- Need properties of prev_n
    let current_n := S prev_n
    have h_current_odd : current_n % 2 = 1 := S_preserves_odd h_prev.1 h_prev.2
    have h_current_pos : current_n > 0 := S_pos prev_n h_prev.2 h_prev.1
    exact ⟨h_current_odd, h_current_pos⟩
    admit -- Need to pass properties through iteration

-- Final Collatz Theorem (Syracuse version)
theorem collatz_Syracuse_terminates (n : ℕ) (hodd : n % 2 = 1) (hn : n > 0) :
    ∃ k, S_iter k n = 1 := by
  -- 1. Establish Boundedness (Axiom)
  obtain ⟨B, h_bound⟩ : ∃ B : ℕ, ∀ k, S_iter k n ≤ B := no_divergence n hn

  -- 2. Finite Orbit Set
  let orbit_set := Set.range (S_iter · n) -- { n, S n, S²n, ... }
  have orbit_finite : orbit_set.Finite := by
    apply Set.finite_bounded_subset_Nat -- Use standard library theorem
    use B; intro x hx; obtain ⟨k, rfl⟩ := Set.mem_range.mp hx; exact h_bound k
    admit -- Need Set.finite_bounded_subset_Nat

  -- 3. Sequence must eventually repeat / enter a cycle
  -- Need non-empty orbit to apply pigeonhole. Orbit contains n, and n>0.
  have orbit_nonempty : orbit_set.Nonempty := Set.range_nonempty _
  obtain ⟨i, j, h_i_lt_j, h_eq⟩ : ∃ i j, i < j ∧ S_iter i n = S_iter j n :=
    Set.Finite.exists_lt_map_eq_of_forall_mem orbit_finite (fun k => S_iter k n) (Set.forall_mem_range.mpr (by intros; linarith))
    admit -- Need exists_lt_map_eq_of_forall_mem and Nat infinite

  -- 4. Identify cycle start m and length k'
  let m := S_iter i n
  let k' := j - i
  have hk'_pos : k' > 0 := Nat.sub_pos_of_lt h_i_lt_j
  have m_cycle : S_iter k' m = m := by
      simp only [S_iter, Nat.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt h_i_lt_j), h_eq]

  -- 5. Use cycle exclusion axiom
  -- Need m > 0 and m % 2 = 1
  have m_prop := S_iter_odd_pos hodd hn i -- Get properties of m
  if hm_eq_1 : m = 1 then
    -- If the cycle element is 1, we have reached 1.
    use i; exact hm_eq_1
  else
    -- m > 1. This is a non-trivial cycle.
    have hm_gt_1 : m > 1 := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr m_prop.2.ne') hm_eq_1
    -- This contradicts the axiom H_no_cycles
    exact no_non_trivial_S_cycles m k' hm_gt_1 m_cycle hk'_pos
  admit -- Need S_iter_odd_pos lemma

-- Theorem relating original Collatz f to Syracuse S
theorem collatz_f_terminates (n : ℕ) (hn : n > 0) : ∃ k, (Nat.iterate f k n) = 1 := by
  -- Reduce to the odd case using S
  if hodd : n % 2 = 1 then
    -- If n=1, result is trivial
    if hn_eq_1 : n = 1 then use 0; rw [hn_eq_1]; rfl
    else
      -- n is odd > 1. Use Syracuse termination.
      have hn_gt_1 : 1 < n := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hn.ne') hn_eq_1
      obtain ⟨k_S, hS_term⟩ := collatz_Syracuse_terminates n hodd hn
      -- Find corresponding k_f
      -- Each S step corresponds to 1 + nu2(3n+1) steps of f
      sorry -- Need to relate k_S to k_f
      admit
  else
    -- n is even > 0. f n = n / 2 < n.
    let n' := n / 2
    have hn'_lt_n : n' < n := Nat.div_lt_self hn (by norm_num)
    have hn'_pos : n' > 0 := Nat.div_pos (Nat.le_of_lt hn) (by norm_num)
    -- Apply result recursively/inductively to n'
    obtain ⟨k', hk'⟩ : ∃ k', (Nat.iterate f k' n') = 1 := by
        apply collatz_f_terminates n' hn'_pos -- Assumes proof works by induction?
        admit
    -- Combine: n -> n' -> ... -> 1
    use k' + 1
    simp only [Nat.iterate_succ_apply, Nat.iterate_one]
    rw [show f n = n' by simp [f, hodd]]
    exact hk'
  admit -- Fix recursive call structure
