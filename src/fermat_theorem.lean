import data.nat.basic
import data.nat.prime
import data.nat.parity
import data.nat.factorial
import tactic.suggest
import data.real.basic
noncomputable theory
open_locale classical

/- we solve this by guess and check, by demonstrating that the only numbers
    that we need to check are 0, 1, and 2, and then checking them. It ended up being
    more difficult to demonstrate that we only need to check 0, 1, and 2 than I thought.  
-/




/-
  this is intended to be used in order to generate things of the form 
  "a ≤ b → a = 0 ∨ ... ∨ a = b". The last one will be leq_succ_0 in order to have a ≤ 0
  replaced with a = 0.
-/
lemma leq_succ (a b : ℕ) : a ≤ b.succ ↔ a ≤ b ∨ a = b.succ :=
begin
  split,
  intro h,
  cases lt_or_eq_of_le h with le eq,
  left,
  exact nat.lt_succ_iff.mp le,
  right,
  exact eq,
  intro h,
  cases h with leq suc,
  exact nat.le_succ_of_le leq,
  exact (eq.symm suc).ge,
end 

/- 
  complementary to the leq_succ, useful for being the last rewrite statement in order to not
  have any inequalities in the term
-/
lemma leq_succ_0 (a : ℕ) : a ≤ 1 ↔ a = 0 ∨ a = 1 := 
begin
  rw ← nat.le_zero_iff,
  exact leq_succ a 0,
end

theorem leq_2_iff (a : ℕ): a ≤ 2 → a = 0 ∨ a = 1 ∨ a = 2 := 
begin 
  induction a,
  intro h,
  left,
  refl,
  intro h,
  have hi : a_n = 0 ∨ a_n = 1 ∨ a_n = 2, {
    have h₂ : a_n ≤ 2, {
      calc a_n ≤ a_n.succ : nat.le_succ a_n
        ...    ≤ 2        : h,
    },
    exact a_ih h₂,
  },
  cases hi with a b,
  right,
  left,
  exact congr_arg nat.succ a,
  cases b with c d,
  right,
  right,
  exact congr_arg nat.succ c,
  have h₃ : a_n.succ > 2, {
    calc a_n.succ > a_n : lt_add_one a_n
     ...          = 2   : d,
  },
  exfalso,
  linarith,
end

theorem leq_3_iff (a : ℕ): a ≤ 3 → a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := 
begin
  rw [leq_succ a 2, leq_succ a 1, leq_succ_0 a],
  tauto,
end

theorem leq (a b : ℕ) : b ≠ 0 → a ∣ b → a ≤ b :=
begin
  intros h div,
  cases div with c hc,
  induction c,
  exfalso,
  rw mul_zero at hc,
  exact h hc,
  induction a,
  linarith,
  have ha : b = a_n.succ * c_n + a_n.succ, {
    calc b = a_n.succ * c_n.succ : hc
      ...  = a_n.succ * (c_n + 1) : rfl
      ...  = a_n.succ * c_n + a_n.succ : by ring,
  },
  rw le_iff_exists_add,
  use a_n.succ * c_n,
  rw add_comm,
  exact ha,
end

theorem prime_2 : nat.prime 2 := 
begin
  split, linarith,
  intros m h,
  have h₂ : m ≤ 2, {
    have h₃ : 2 ≠ 0, {exact two_ne_zero,},
    exact (leq m 2) h₃ h,
  },
  have h₃ : m = 0 ∨ m = 1 ∨ m = 2, {
    exact leq_2_iff m h₂,
  },
  cases h₃ with a b,
  exfalso,
  cases h with c hc,
  rw [a,zero_mul] at hc,
  linarith,
  exact b,
end

theorem prime_3 : nat.prime 3 := 
begin
  split, linarith,
  intros m hm,
  have hl : m ≤ 3, {
    have neq : 3 ≠ 0, {linarith,},
    exact (leq m 3) neq hm,
  },
  have h : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3, {exact leq_3_iff m hl,},
  cases h with zero h,
  {
    cases hm with c hc,
    rw zero at hc,
    rw zero_mul at hc,
    exfalso,
    linarith,
  },
  cases h with one h,
  {
    left,
    exact one,
  },
  cases h with two three,
  {
    exfalso,
    cases hm with c hc,
    rw two at hc,
    have h₁ : odd 3, {
      exact odd_bit1 1,
    },
    have h₂ : even (2 * c), {
      use c,
    },
    have h₃ : even 3, {
      rw ← hc at h₂,
      exact h₂,
    },
    have h₄ : ¬(even 3), {
      rw←nat.odd_iff_not_even,
      exact h₁,
    },
    exact h₄ h₃,
  },
  right, 
  exact three,
end

theorem not_prime_4 : ¬ nat.prime 4 := 
begin
  unfold nat.prime,
  push_neg,
  intro h,
  use 2,
  split,
  use 2,
  linarith,
  split,
  intro h,
  linarith,
  intro h,
  linarith,
end

theorem prime_5 : nat.prime 5 :=
begin
  split,
  linarith,
  intros n h,
  have h5 : 5 ≠ 0, {linarith,},
  have hl : n ≤ 5, {exact leq _ _ h5 h,},
  have hor : n=0∨n=1∨n=2∨n=3∨n=4∨n=5, {
    rw [leq_succ n 4, leq_succ n 3, leq_succ n 2, leq_succ n 1, leq_succ_0 n] at hl,
    tauto,
  },  
  cases hor with zero hor,
  {
    exfalso,
    cases h with c hc,
    rw zero at hc,
    have hzero : 5 = 0, {linarith,},
    exact h5 hzero,
  },
  cases hor with one hor,
  {
    left,
    exact one,
  },
  cases hor with two hor,
  {
    cases h with c h,
    rw two at h,
    sorry,
  },
  sorry,
end