namespace nat

def twice (f : ℕ → ℕ) (a : ℕ) :=
  f (f a)

theorem testTheorem : twice (λ x, x + 2) 2 = 6 :=
begin
  refl,
end

end nat