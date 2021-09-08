import data.nat.basic
import tactic.ring
import tactic
noncomputable theory
open_locale classical
open nat

-- "a mod b = c"
def mod (a b c : ℕ) := c < b ∧ ∃ (d : ℕ), d * b + c = a

/- 
  Main theorem of this file. Used in the prime number file in order to check for primes faster
-/
theorem mod_neq_0_not_div (a b : ℕ) : (∃ (c : ℕ), c ≠ 0 ∧ mod a b c) ↔ ¬ b ∣ a :=
begin
  split,
  intros h div,
  cases h with c hc,
  have hl := hc.left,
  cases hc.right.right with d hd,
  have hf := hc.right.left,
  cases div with e he,
  rw he at hd,
  have hg : c = b * (e - d), {
    calc c = b * e - d * b      : (norm_num.sub_nat_pos (b * e) (d * b) c hd).symm
      ...  = b * e - b * d      : by ring_nf
      ...  = b * (e - d)        : (nat.mul_sub_left_distrib b e d).symm, 
  },
  have hee : (e-d) = 0 ∨ (e-d) ≥ 1, {exact (e - d).eq_zero_or_pos,},
  cases hee with zero one,
  rw zero at hg,
  rw mul_zero at hg,
  exact hl hg,
  have hee : c ≥ b, {
    calc c = b * (e - d) : hg
      ...  ≥ b * 1       : mul_le_mul_left' one b
      ...  = b           : by rw mul_one,
  },
  linarith,
  contrapose!,
  intro h,
  sorry,

  end 