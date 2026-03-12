import Verif.Expr

open verif

/-
w = w':
  expr₁ + r₁ = expr'₁ + r'₁
  expr₂      = expr'₂
  expr₃ + r₃ = expr'₃ + r'₃

1-
r'₁ =>
r'₂ =>
r'₃ =>
r'₄ =>

2- (rewrote r'₁) [r'₁ := expr₁ + r₁ + expr'₁]
r'₁ =>
r'₂ =>
r'₃ => r'₁
r'₄ => r'₁

3- (failed in rewriting r'₃)
r'₁ => r'₃          -- this would be a self-reference
r'₂ =>
r'₃ => r'₁
r'₄ => r'₁
-/
