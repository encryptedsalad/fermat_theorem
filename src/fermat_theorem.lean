import data.nat.basic
import data.nat.prime

theorem add_commutative (a b : ℕ) : a + b = b + a := 
begin
  exact add_comm a b,
end

theorem infinitude_of_primes : ∀ a : ℕ, ∃ b : ℕ, b > a ∧ nat.prime b :=
begin
  sorry,
end 
