/-
# Compiler Correctness via Computational Paths

Source and target languages, compilation functions, semantic preservation,
optimization passes, correctness composition, all via computational paths.

## References

- Leroy, "Formal Verification of a Realistic Compiler"
- Chlipala, "A Verified Compiler for an Impure Functional Language"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace CompilerPaths

universe u v

open ComputationalPaths.Path

/-! ## Source Language -/

/-- Source language expressions. -/
inductive SrcExpr where
  | lit : Int → SrcExpr
  | add : SrcExpr → SrcExpr → SrcExpr
  | mul : SrcExpr → SrcExpr → SrcExpr
  | neg : SrcExpr → SrcExpr
  deriving Repr, BEq, DecidableEq

/-- Source language evaluation. -/
def srcEval : SrcExpr → Int
  | .lit n => n
  | .add e1 e2 => srcEval e1 + srcEval e2
  | .mul e1 e2 => srcEval e1 * srcEval e2
  | .neg e => -(srcEval e)

/-- Evaluation of a literal. -/
theorem srcEval_lit (n : Int) : srcEval (.lit n) = n := rfl

/-- Evaluation of addition. -/
theorem srcEval_add (e1 e2 : SrcExpr) :
    srcEval (.add e1 e2) = srcEval e1 + srcEval e2 := rfl

/-- Evaluation of multiplication. -/
theorem srcEval_mul (e1 e2 : SrcExpr) :
    srcEval (.mul e1 e2) = srcEval e1 * srcEval e2 := rfl

/-- Evaluation of negation. -/
theorem srcEval_neg (e : SrcExpr) :
    srcEval (.neg e) = -(srcEval e) := rfl

/-- Path from source expression equality. -/
def srcEvalPath {e1 e2 : SrcExpr} (h : e1 = e2) :
    Path (srcEval e1) (srcEval e2) :=
  Path.congrArg srcEval (Path.ofEq h)

/-! ## Target Language (Stack Machine) -/

/-- Stack machine instructions. -/
inductive Instr where
  | push : Int → Instr
  | iadd : Instr
  | imul : Instr
  | ineg : Instr
  deriving Repr, BEq, DecidableEq

/-- A stack is a list of integers. -/
abbrev Stack := List Int

/-- Execute a single instruction on a stack. -/
def execInstr (i : Instr) (s : Stack) : Stack :=
  match i, s with
  | .push n, s => n :: s
  | .iadd, a :: b :: rest => (b + a) :: rest
  | .imul, a :: b :: rest => (b * a) :: rest
  | .ineg, a :: rest => (-a) :: rest
  | _, s => s

/-- Execute a program (list of instructions) on a stack. -/
def execProg : List Instr → Stack → Stack
  | [], s => s
  | i :: rest, s => execProg rest (execInstr i s)

/-- Empty program preserves stack. -/
theorem execProg_nil (s : Stack) : execProg [] s = s := rfl

/-- Single instruction execution. -/
theorem execProg_cons (i : Instr) (rest : List Instr) (s : Stack) :
    execProg (i :: rest) s = execProg rest (execInstr i s) := rfl

/-- Push instruction adds to stack. -/
theorem execInstr_push (n : Int) (s : Stack) :
    execInstr (.push n) s = n :: s := rfl

/-- Program concatenation semantics. -/
theorem execProg_append (p1 p2 : List Instr) (s : Stack) :
    execProg (p1 ++ p2) s = execProg p2 (execProg p1 s) := by
  induction p1 generalizing s with
  | nil => rfl
  | cons i rest ih => exact ih (execInstr i s)

/-! ## Compilation -/

/-- Compile a source expression to stack machine code. -/
def compile : SrcExpr → List Instr
  | .lit n => [Instr.push n]
  | .add e1 e2 => compile e1 ++ compile e2 ++ [Instr.iadd]
  | .mul e1 e2 => compile e1 ++ compile e2 ++ [Instr.imul]
  | .neg e => compile e ++ [Instr.ineg]

/-- Compilation of literal. -/
theorem compile_lit (n : Int) : compile (.lit n) = [Instr.push n] := rfl

/-- Compilation of negation. -/
theorem compile_neg (e : SrcExpr) :
    compile (.neg e) = compile e ++ [Instr.ineg] := rfl

/-! ## Compiler Correctness -/

/-- Main correctness theorem: compiled code pushes the evaluation result. -/
theorem compile_correct (e : SrcExpr) (s : Stack) :
    execProg (compile e) s = srcEval e :: s := by
  induction e generalizing s with
  | lit n => rfl
  | add e1 e2 ih1 ih2 =>
    simp only [compile, srcEval, execProg_append]
    rw [ih1, ih2]; rfl
  | mul e1 e2 ih1 ih2 =>
    simp only [compile, srcEval, execProg_append]
    rw [ih1, ih2]; rfl
  | neg e ih =>
    simp only [compile, srcEval, execProg_append]
    rw [ih]; rfl

/-- Path from compiler correctness. -/
def compile_correct_path (e : SrcExpr) (s : Stack) :
    Path (execProg (compile e) s) (srcEval e :: s) :=
  Path.ofEq (compile_correct e s)

/-- Compiled program on empty stack yields singleton. -/
theorem compile_correct_empty (e : SrcExpr) :
    execProg (compile e) [] = [srcEval e] :=
  compile_correct e []

/-- Path from empty stack correctness. -/
def compile_correct_empty_path (e : SrcExpr) :
    Path (execProg (compile e) []) [srcEval e] :=
  Path.ofEq (compile_correct_empty e)

/-! ## Optimization Passes -/

/-- Constant folding optimization on source expressions. -/
def constFold : SrcExpr → SrcExpr
  | .add (.lit a) (.lit b) => .lit (a + b)
  | .mul (.lit a) (.lit b) => .lit (a * b)
  | .neg (.lit a) => .lit (-a)
  | .add e1 e2 => .add (constFold e1) (constFold e2)
  | .mul e1 e2 => .mul (constFold e1) (constFold e2)
  | .neg e => .neg (constFold e)
  | e => e

/-- Constant folding preserves semantics for literals. -/
theorem constFold_lit (n : Int) : srcEval (constFold (.lit n)) = srcEval (.lit n) := rfl

/-- Literal identity optimization (replaces lit n with lit n). -/
def litIdOpt : SrcExpr → SrcExpr
  | .lit n => .lit n
  | .add e1 e2 => .add (litIdOpt e1) (litIdOpt e2)
  | .mul e1 e2 => .mul (litIdOpt e1) (litIdOpt e2)
  | .neg e => .neg (litIdOpt e)

/-- Literal identity optimization preserves semantics. -/
theorem litIdOpt_correct (e : SrcExpr) :
    srcEval (litIdOpt e) = srcEval e := by
  induction e with
  | lit _ => rfl
  | add _ _ ih1 ih2 => simp [litIdOpt, srcEval, ih1, ih2]
  | mul _ _ ih1 ih2 => simp [litIdOpt, srcEval, ih1, ih2]
  | neg _ ih => simp [litIdOpt, srcEval, ih]

/-- Path from literal identity optimization correctness. -/
def litIdOpt_path (e : SrcExpr) :
    Path (srcEval (litIdOpt e)) (srcEval e) :=
  Path.ofEq (litIdOpt_correct e)

/-- Identity optimization (no-op). -/
def idOpt : SrcExpr → SrcExpr := fun e => e

/-- Identity optimization is correct. -/
theorem idOpt_correct (e : SrcExpr) : srcEval (idOpt e) = srcEval e := rfl

/-! ## Optimization Composition -/

/-- Compose two optimizations. -/
def composeOpt (f g : SrcExpr → SrcExpr) : SrcExpr → SrcExpr := f ∘ g

/-- Composition preserves semantics if both passes do. -/
theorem composeOpt_correct
    (f g : SrcExpr → SrcExpr)
    (hf : ∀ e, srcEval (f e) = srcEval e)
    (hg : ∀ e, srcEval (g e) = srcEval e)
    (e : SrcExpr) :
    srcEval (composeOpt f g e) = srcEval e := by
  simp [composeOpt, Function.comp, hf, hg]

/-- Path from composed optimization correctness. -/
def composeOpt_path
    (f g : SrcExpr → SrcExpr)
    (hf : ∀ e, srcEval (f e) = srcEval e)
    (hg : ∀ e, srcEval (g e) = srcEval e)
    (e : SrcExpr) :
    Path (srcEval (composeOpt f g e)) (srcEval e) :=
  Path.ofEq (composeOpt_correct f g hf hg e)

/-- Triple composition of optimizations. -/
theorem composeOpt_assoc (f g h : SrcExpr → SrcExpr) :
    composeOpt (composeOpt f g) h = composeOpt f (composeOpt g h) := rfl

/-- Identity is left unit of composition. -/
theorem composeOpt_id_left (f : SrcExpr → SrcExpr) :
    composeOpt idOpt f = f := rfl

/-- Identity is right unit of composition. -/
theorem composeOpt_id_right (f : SrcExpr → SrcExpr) :
    composeOpt f idOpt = f := rfl

/-! ## End-to-End Correctness -/

/-- End-to-end correctness: optimize then compile. -/
theorem optimize_compile_correct
    (opt : SrcExpr → SrcExpr)
    (hopt : ∀ e, srcEval (opt e) = srcEval e)
    (e : SrcExpr) (s : Stack) :
    execProg (compile (opt e)) s = srcEval e :: s := by
  rw [compile_correct, hopt]

/-- Path from end-to-end correctness. -/
def optimize_compile_path
    (opt : SrcExpr → SrcExpr)
    (hopt : ∀ e, srcEval (opt e) = srcEval e)
    (e : SrcExpr) (s : Stack) :
    Path (execProg (compile (opt e)) s) (srcEval e :: s) :=
  Path.ofEq (optimize_compile_correct opt hopt e s)

/-- CongrArg: equal source yields equal compiled code. -/
theorem compile_congrArg {e1 e2 : SrcExpr} (h : e1 = e2) :
    compile e1 = compile e2 := by subst h; rfl

/-- Path from compilation congruence. -/
def compile_congrArg_path {e1 e2 : SrcExpr} (h : e1 = e2) :
    Path (compile e1) (compile e2) :=
  Path.congrArg compile (Path.ofEq h)

/-- Symmetry: correctness path is invertible. -/
def compile_correct_symm (e : SrcExpr) (s : Stack) :
    Path (srcEval e :: s) (execProg (compile e) s) :=
  Path.symm (compile_correct_path e s)

/-- Transitivity: chain correctness with optimization. -/
def compile_chain (e : SrcExpr)
    (opt : SrcExpr → SrcExpr)
    (hopt : ∀ e, srcEval (opt e) = srcEval e)
    (s : Stack) :
    Path (execProg (compile (opt e)) s) (srcEval e :: s) :=
  Path.trans
    (Path.ofEq (compile_correct (opt e) s))
    (Path.ofEq (_root_.congrArg (· :: s) (hopt e)))

/-- Transport stack property along correctness path. -/
def correctness_transport (e : SrcExpr) (s : Stack)
    (P : Stack → Prop) (hp : P (srcEval e :: s)) :
    P (execProg (compile e) s) :=
  Path.transport (D := P) (compile_correct_symm e s) hp

end CompilerPaths
end Computation
end Path
end ComputationalPaths
