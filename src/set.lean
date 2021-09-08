import data.nat.basic
import tactic.ring
import tactic
noncomputable theory
open_locale classical
open nat
open set

variable {α : Type}
variables { a b c : set α}

theorem first_theorem : a ∩ b ⊆ a := 
begin
  intros x h,
  exact h.left,
end

theorem second_theorem : a ∩ b = b ∩ a := 
begin
  ext x,
  split,
  intro h,
  exact ⟨h.right, h.left⟩,
  intro h,
  exact ⟨h.right, h.left⟩,
end

theorem third_theorem : a ⊆ a ∪ b := 
begin
  intros x h,
  left,
  exact h,
end



