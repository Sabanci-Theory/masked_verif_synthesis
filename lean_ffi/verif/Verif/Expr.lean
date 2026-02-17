namespace verif

-- Q: Should we include Public?
inductive VarType
  | Secret   : String → VarType
  | Random   : String → VarType
  deriving Repr, DecidableEq, Inhabited

inductive Expr
  | var  : VarType → Expr
  | val  : Bool → Expr
  | not  : Expr → Expr
  | and  : Expr → Expr → Expr
  | xor  : Expr → Expr → Expr
  | or   : Expr → Expr → Expr
  deriving Repr, DecidableEq, Inhabited

abbrev Assignment := VarType → Bool

def Expr.eval (env : Assignment) : Expr → Bool
  | var v     => env v
  | val b     => b
  | not e     => !(e.eval env)
  | and e1 e2 => (e1.eval env) && (e2.eval env)
  | xor e1 e2 => (e1.eval env) != (e2.eval env)
  | or e1 e2  => (e1.eval env) || (e2.eval env)

open VarType
open Expr

def x0 := var (Secret "x0")
def y0 := var (Secret "y0")
def r  := var (Random "r")

def masked_expr : Expr := xor (and x0 y0) r

#print masked_expr

def testEnv : Assignment
  | Secret "x0" => true
  | Secret "y0" => true
  | Random "r"  => false
  | _           => false

#eval masked_expr.eval testEnv

end verif
