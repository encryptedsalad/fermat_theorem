import data.nat.basic
import tactic.ring
noncomputable theory
open_locale classical
open nat


def power : ℕ → ℕ → ℕ
| n zero := 1
| n (succ x) := power n x * n



theorem power_add (a b c : ℕ) : (power a b) * (power a c) = (power a (b + c)) :=
begin
  induction c with c hyp,
  calc power a b * power a 0 
        = power a b * 1   : rfl
    ... = power a b       : by rw mul_one
    ... = power a (b + 0) : rfl,
  
  calc (power a b)*(power a(c+1)) 
        = (power a b) * ((power a c) * a) : rfl
    ... = (power a b * power a c) * a     : by ring
    ... = power a (b + c) * a             : by rw hyp
    ... = power a (b + c + 1)             : rfl,
end

theorem power_down (a b c : ℕ) : power (power a b) c = power a (b * c) := 
begin
  induction c with c hyp,
  
  -- base case
  calc power (power a b) 0
        = 1               : rfl
    ... = power a 0       : rfl
    ... = power a (b * 0) : rfl,

  -- induction step
  calc power (power a b) (c + 1) 
        = power (power a b) c * (power a b) : rfl
    ... = power a (b * c) * (power a b)     : by rw hyp
    ... = power a (b * c + b)               : by rw power_add a (b * c) b
    ... = power a (b * (c + 1))             : rfl,
end


