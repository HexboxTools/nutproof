variable {F : Type} [Lean.Grind.Field F]
example (k y r : F) : k*(y + r) - r*k = k*y := by grind
example (s s' e e' k : F) (h : s - e*k = s' - e'*k) (hne : e ≠ e') : k = (s - s')/(e - e') := by grind
