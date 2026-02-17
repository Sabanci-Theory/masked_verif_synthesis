import Std.Data.HashMap
import Std.Internal.Parsec
import Verif.Expr

open Std (HashMap)
open Std.Internal.Parsec
open Std.Internal.Parsec.String
open verif

/- helper structures to keep track of the state while parsing -/

structure CircuitContext where
  secrets : HashMap String Unit := HashMap.emptyWithCapacity
  randoms : HashMap String Unit := HashMap.emptyWithCapacity
  wires   : HashMap String Expr := HashMap.emptyWithCapacity

inductive RawStmt
  | declSecrets : List String → RawStmt
  | declRandoms : List String → RawStmt
  | assign      : String → String → Char → String → RawStmt
  | noOp        : RawStmt
  deriving Repr

/- parser functions -/

-- skips one or more whitespace(s)
def skipSpace : Parser Unit := do
  let _ ← many (satisfy fun c => c.isWhitespace)
  return ()

-- parses the identifiers
def parseIdent : Parser String := do
  let s ← many1 (satisfy fun c => c.isAlphanum)
  return String.ofList s.toList

-- parses identifiers one after another (used for Secrets and Randoms in the header)
def parseIdentList : Parser (List String) := do
  let arr ← many (do skipSpace; parseIdent)
  return arr.toList

-- parses the Secrets header
def parseSecretsDecl : Parser RawStmt := do
  skipString "-- Secrets:"
  let vars ← parseIdentList
  return RawStmt.declSecrets vars

-- parses the Randoms header
def parseRandomsDecl : Parser RawStmt := do
  skipString "-- Randoms:"
  let vars ← parseIdentList
  return RawStmt.declRandoms vars

-- parses an assignment
def parseAssignment : Parser RawStmt := do
  let target ← parseIdent
  skipSpace
  let _ ← skipChar '='
  skipSpace
  let op1 ← parseIdent
  skipSpace
  -- Parse operator char
  let operator ← satisfy fun c => c == '+' || c == '*'
  skipSpace
  let op2 ← parseIdent
  return RawStmt.assign target op1 operator op2

-- line by line parsing happens here
def parseLine : Parser RawStmt := do
  skipSpace
  (attempt parseSecretsDecl)
  <|> (attempt parseRandomsDecl)
  <|> (attempt parseAssignment)
  <|> return RawStmt.noOp

/- inlining and bookkeeping functions -/

-- inlines the wires
def resolve (ctx : CircuitContext) (name : String) : Except String Expr := do
  if ctx.wires.contains name then
    return ctx.wires.get! name
  else if ctx.secrets.contains name then
    return Expr.var (VarType.Secret name)
  else if ctx.randoms.contains name then
    return Expr.var (VarType.Random name)
  else
    throw s!"Unknown variable '{name}'"

-- processes a single line of statement
def processStmt (ctx : CircuitContext) (stmt : RawStmt)
    : Except String (CircuitContext × Option (String × Expr)) := do
  match stmt with
  | RawStmt.noOp =>
      return (ctx, none)

  | RawStmt.declSecrets names =>
      let newSecrets := names.foldl (fun m n => m.insert n ()) ctx.secrets
      return ({ ctx with secrets := newSecrets }, none)

  | RawStmt.declRandoms names =>
      let newRandoms := names.foldl (fun m n => m.insert n ()) ctx.randoms
      return ({ ctx with randoms := newRandoms }, none)

  | RawStmt.assign target lhsName opChar rhsName =>
      let lhsExpr ← resolve ctx lhsName
      let rhsExpr ← resolve ctx rhsName

      let opExpr ← match opChar with
        | '+' => pure (Expr.xor lhsExpr rhsExpr)
        | '*' => pure (Expr.and lhsExpr rhsExpr)
        | _   => throw s!"Unknown operator '{opChar}'"

      let newWires := ctx.wires.insert target opExpr
      return ({ ctx with wires := newWires }, some (target, opExpr))

/- main functions -/

def parseCircuit (input : String) : Except String (List (String × Expr)) := do
  let lines := input.splitOn "\n"

  let (_, results) ← lines.foldlM (init := ({}, []))
    fun (ctx : CircuitContext × List (String × Expr)) lineStr => do
      let (currentCtx, acc) := ctx

      match Parser.run parseLine lineStr with
      | .ok stmt =>
          let (nextCtx, resOpt) ← processStmt currentCtx stmt
          match resOpt with
          | some res => return (nextCtx, acc ++ [res])
          | none     => return (nextCtx, acc)
      | .error e => throw s!"Parse Error on line '{lineStr}': {e}"

  return results

def parseFile (filePath : System.FilePath) : IO (List (String × Expr)) := do
  let fileContent ← IO.FS.readFile filePath

  match parseCircuit fileContent with
  | .ok results   => return results
  | .error errMsg =>
    throw (IO.userError s!"\nFile: {filePath}\nError: {errMsg}")

def main : IO Unit := do
  let fileName := "2_share_dom_and.txt"
  let path : System.FilePath := "Verif" / "netlists" / fileName

  try
    let circuit ← parseFile path

    for (name, expr) in circuit do
      IO.println s!"  {name} := {repr expr}"
  catch e =>
    IO.println s!"Error: {e}"

#eval main
