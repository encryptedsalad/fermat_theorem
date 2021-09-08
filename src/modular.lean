import data.nat.basic
import tactic.ring
import tactic
noncomputable theory
open_locale classical
open nat

-- "a mod b = c"
def mod (a b c : ℕ) := c < b ∧ ∃ (d : ℕ), d * b + c = a

theorem mod_2 : mod 1 2 1 :=
begin
  split, linarith,
  use 0, ring,
end




