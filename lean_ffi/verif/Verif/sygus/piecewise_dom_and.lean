import cvc5
open cvc5

def mkBitVectorVal (tm : TermManager) (width : Nat) (val : Int) : Env Term := do
  let intVal ← tm.mkInteger val
  let op ← tm.mkOpOfIndices Kind.INT_TO_BITVECTOR #[width]
  tm.mkTermOfOp op #[intVal]

def sygusProblem : Env Unit := do
  let tm ← TermManager.new
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"

  solver.setLogic "BV"

  let bv1 ← tm.mkBitVectorSort 1

  let b0 ← mkBitVectorVal tm 1 0
  let b1 ← mkBitVectorVal tm 1 1

  let pT1 ← tm.mkParamSort "T1"
  let pT2 ← tm.mkParamSort "T2"
  let pairCtorDecl ← tm.mkDatatypeConstructorDecl "mk-pair"
  let pairCtorDecl ← pairCtorDecl.addSelector "first" pT1
  let pairCtorDecl ← pairCtorDecl.addSelector "second" pT2
  let pairDecl ← tm.mkDatatypeDecl "Pair" #[pT1, pT2]
  let pairDecl ← pairDecl.addConstructor pairCtorDecl
  let pairSortGeneric ← tm.mkDatatypeSort pairDecl

  let rT1 ← tm.mkParamSort "T1"
  let rT2 ← tm.mkParamSort "T2"
  let rT3 ← tm.mkParamSort "T3"
  let randsCtorDecl ← tm.mkDatatypeConstructorDecl "mk-rands"
  let randsCtorDecl ← randsCtorDecl.addSelector "r0" rT1
  let randsCtorDecl ← randsCtorDecl.addSelector "r1" rT2
  let randsCtorDecl ← randsCtorDecl.addSelector "r2" rT3
  let randsDecl ← tm.mkDatatypeDecl "Rands" #[rT1, rT2, rT3]
  let randsDecl ← randsDecl.addConstructor randsCtorDecl
  let randsSortGeneric ← tm.mkDatatypeSort randsDecl

  -----------------------------------------------------------------------------
  -- Instantiate datatypes
  -----------------------------------------------------------------------------
  let pairSort ← pairSortGeneric.instantiate #[bv1, bv1]

  -- Rands (BitVec 1) (BitVec 1) (BitVec 1)
  let randsSort ← randsSortGeneric.instantiate #[bv1, bv1, bv1]

  -- Get accessors
  let dtPair ← pairSortGeneric.getDatatype
  let cMkPair ← dtPair.getConstructor "mk-pair"
  let tMkPair ← cMkPair.getTerm
  let tFirst  ← (← cMkPair.getSelector "first").getTerm
  let tSecond ← (← cMkPair.getSelector "second").getTerm

  let dtRands ← randsSortGeneric.getDatatype
  let cMkRands ← dtRands.getConstructor "mk-rands"
  let tMkRands ← cMkRands.getTerm
  let tR0 ← (← cMkRands.getSelector "r0").getTerm
  let tR1 ← (← cMkRands.getSelector "r1").getTerm
  let tR2 ← (← cMkRands.getSelector "r2").getTerm

  -----------------------------------------------------------------------------
  -- Configuration
  -----------------------------------------------------------------------------

  -- w
  let mk_w (a b r : Term) : Env Term := do
    let r0 ← tm.mkTerm Kind.APPLY_SELECTOR #[tR0, r]
    let r1 ← tm.mkTerm Kind.APPLY_SELECTOR #[tR1, r]
    let r2 ← tm.mkTerm Kind.APPLY_SELECTOR #[tR2, r]

    let term1 ← tm.mkTerm Kind.BITVECTOR_XOR #[
      ← tm.mkTerm Kind.BITVECTOR_AND #[a, r1],
      ← tm.mkTerm Kind.BITVECTOR_AND #[r0, r1]
    ]

    let term2 ← tm.mkTerm Kind.BITVECTOR_XOR #[
      ← tm.mkTerm Kind.BITVECTOR_AND #[b, r0],
      ← tm.mkTerm Kind.BITVECTOR_XOR #[
        ← tm.mkTerm Kind.BITVECTOR_AND #[r0, r1],
        r2
      ]
    ]

    tm.mkTerm Kind.APPLY_CONSTRUCTOR #[tMkPair, term1, term2]

  -----------------------------------------------------------------------------
  -- Synthesis setup
  -----------------------------------------------------------------------------

  -- Define bound variables for the synthesis functions: f0(a, b, ap, bp, r)
  let bound_a  ← tm.mkVar bv1 "a"
  let bound_b  ← tm.mkVar bv1 "b"
  let bound_ap ← tm.mkVar bv1 "ap"
  let bound_bp ← tm.mkVar bv1 "bp"
  let bound_r  ← tm.mkVar randsSort "r"
  let boundVars := #[bound_a, bound_b, bound_ap, bound_bp, bound_r]

  -- Grammar non-terminals
  let ntS    ← tm.mkVar bv1 "S"
  let ntCond ← tm.mkVar (← tm.getBooleanSort) "Cond"
  let ntB    ← tm.mkVar bv1 "B"
  let ntSymbols := #[ntS, ntCond, ntB]

  -- Create grammar
  let grammar ← solver.mkGrammar boundVars ntSymbols

  -- (S (_ BitVec 1) (B (ite Cond S S)))
  let ruleS_B ← pure ntB
  let ruleS_Ite ← tm.mkTerm Kind.ITE #[ntCond, ntS, ntS]
  let grammar ← grammar.addRules ntS #[ruleS_B, ruleS_Ite]

  -- (Cond Bool ((= ap #b0)))
  let ruleCond ← tm.mkTerm Kind.EQUAL #[bound_ap, b0]
  let grammar ← grammar.addRule ntCond ruleCond

  -- (B (_ BitVec 1) ((bvxor a (r0 r)) ap (r0 r) (r1 r) #b1 (bvxor B B) (bvand B B)))
  let r0_r ← tm.mkTerm Kind.APPLY_SELECTOR #[tR0, bound_r]
  let r1_r ← tm.mkTerm Kind.APPLY_SELECTOR #[tR1, bound_r]

  let b_term1 ← tm.mkTerm Kind.BITVECTOR_XOR #[bound_a, r0_r]
  let b_term2 := bound_ap
  let b_term3 := r0_r
  let b_term4 := r1_r
  let b_term5 := b1
  let b_term6 ← tm.mkTerm Kind.BITVECTOR_XOR #[ntB, ntB]
  let b_term7 ← tm.mkTerm Kind.BITVECTOR_AND #[ntB, ntB]

  let grammar ← grammar.addRules ntB #[b_term1, b_term2, b_term3, b_term4, b_term5, b_term6, b_term7]

  -- Synthesize f0 and f1
  let f0 ← solver.synthFun "f0" boundVars bv1 (some grammar)
  let f1 ← solver.synthFun "f1" boundVars bv1 (some grammar)

  -- f2 = ((b + r1) * r0) + r2 + ((bp + _1) * _0)
  let mk_f2 (b bp r f0_val f1_val : Term) : Env Term := do
    let r0 ← tm.mkTerm Kind.APPLY_SELECTOR #[tR0, r]
    let r1 ← tm.mkTerm Kind.APPLY_SELECTOR #[tR1, r]
    let r2 ← tm.mkTerm Kind.APPLY_SELECTOR #[tR2, r]

    let p1 ← tm.mkTerm Kind.BITVECTOR_XOR #[b, r1]
    let p2 ← tm.mkTerm Kind.BITVECTOR_AND #[p1, r0]
    let p3 ← tm.mkTerm Kind.BITVECTOR_XOR #[p2, r2]

    let p4 ← tm.mkTerm Kind.BITVECTOR_XOR #[bp, f1_val]
    let p5 ← tm.mkTerm Kind.BITVECTOR_AND #[p4, f0_val]

    tm.mkTerm Kind.BITVECTOR_XOR #[p3, p5]

  -----------------------------------------------------------------------------
  -- Constraints
  -----------------------------------------------------------------------------

  -- Declare SyGuS universal variables
  let a  ← solver.declareSygusVar "a" bv1
  let b  ← solver.declareSygusVar "b" bv1
  let r  ← solver.declareSygusVar "r" randsSort
  let ap ← solver.declareSygusVar "ap" bv1
  let bp ← solver.declareSygusVar "bp" bv1
  let rp ← solver.declareSygusVar "rp" randsSort

  let applyF (f : Term) (args : Array Term) : Env Term :=
    tm.mkTerm Kind.APPLY_UF (#[f] ++ args)

  let args := #[a, b, ap, bp, r]
  let f0_app ← applyF f0 args
  let f1_app ← applyF f1 args

  let f2_res ← mk_f2 b bp r f0_app f1_app

  -- (= (w a b r) (w ap bp (mk-rands f0 f1 f2)))
  let w_lhs ← mk_w a b r

  let r_constructed ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[tMkRands, f0_app, f1_app, f2_res]
  let w_rhs ← mk_w ap bp r_constructed

  let constraint1 ← tm.mkTerm Kind.EQUAL #[w_lhs, w_rhs]
  solver.addSygusConstraint constraint1

  -- (=> (and (= f0 fp0) (= f1 fp1) (= f2 f2p)) (= r rp))
  let args_p := #[a, b, ap, bp, rp]
  let fp0_app ← applyF f0 args_p
  let fp1_app ← applyF f1 args_p
  let fp2_res ← mk_f2 b bp rp fp0_app fp1_app

  let f2_orig ← mk_f2 b bp r f0_app f1_app

  let eq_f0 ← tm.mkTerm Kind.EQUAL #[f0_app, fp0_app]
  let eq_f1 ← tm.mkTerm Kind.EQUAL #[f1_app, fp1_app]
  let eq_f2 ← tm.mkTerm Kind.EQUAL #[f2_orig, fp2_res]

  let and_cond ← tm.mkTerm Kind.AND #[eq_f0, eq_f1, eq_f2]
  let eq_r ← tm.mkTerm Kind.EQUAL #[r, rp]

  let constraint2 ← tm.mkTerm Kind.IMPLIES #[and_cond, eq_r]
  solver.addSygusConstraint constraint2

  -----------------------------------------------------------------------------
  -- Check synthesis
  -----------------------------------------------------------------------------

  let result ← solver.checkSynth
  IO.println s!"Result: {result}"

  if result.hasSolution then
    let sols ← solver.getSynthSolutions #[f0, f1]
    IO.println s!"Solution f0: {sols[0]!}"
    IO.println s!"Solution f1: {sols[1]!}"

def main : IO Unit := do
  let _ ← sygusProblem.runIO

#eval main
