/-
# Denotational Semantics via Computational Paths

This module models denotational semantics using computational paths:
semantic domains, meaning functions as path maps, compositionality
as path functoriality, environment paths, and the substitution lemma
as path naturality.

## References

- Stoy, "Denotational Semantics"
- Winskel, "The Formal Semantics of Programming Languages"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace DenotationalPaths

universe u v

open ComputationalPaths.Path

/-! ## Syntax as Inductive Types -/

/-- Simple expression language. -/
inductive Expr where
  | lit : Nat → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | letE : Nat → Expr → Expr → Expr
  deriving Repr, BEq

/-- Simple statement language. -/
inductive Stmt where
  | skip : Stmt
  | assign : Nat → Expr → Stmt
  | seq : Stmt → Stmt → Stmt
  deriving Repr, BEq

/-! ## Environments as Path Structures -/

/-- An environment maps variables to values, wrapped for path usage. -/
structure Env where
  lookup : Nat → Nat
  deriving Repr, BEq

/-- Update an environment at a given variable. -/
def Env.update (env : Env) (x : Nat) (v : Nat) : Env :=
  ⟨fun y => if y == x then v else env.lookup y⟩

/-- Environment update at a variable retrieves the new value. -/
theorem env_update_same (env : Env) (x : Nat) (v : Nat) :
    (env.update x v).lookup x = v := by
  simp [Env.update]

/-- Environment update at a different variable retrieves the old value. -/
theorem env_update_other (env : Env) (x y : Nat) (v : Nat) (h : y != x) :
    (env.update x v).lookup y = env.lookup y := by
  simp [Env.update]
  intro heq
  rw [heq] at h
  simp at h

/-- Path between environments: they agree on all variables. -/
def envPath (e1 e2 : Env) (h : e1 = e2) : Path e1 e2 :=
  Path.ofEq h

/-! ## Meaning Functions -/

/-- Expression denotation: maps an expression and environment to a value. -/
def evalExpr (env : Env) : Expr → Nat
  | Expr.lit n => n
  | Expr.var x => env.lookup x
  | Expr.add e1 e2 => evalExpr env e1 + evalExpr env e2
  | Expr.letE x e1 e2 => evalExpr (env.update x (evalExpr env e1)) e2

/-- Statement denotation: maps a statement and environment to a new environment. -/
def evalStmt (env : Env) : Stmt → Env
  | Stmt.skip => env
  | Stmt.assign x e => env.update x (evalExpr env e)
  | Stmt.seq s1 s2 => evalStmt (evalStmt env s1) s2

/-- Skip is the identity on environments. -/
theorem eval_skip (env : Env) : evalStmt env Stmt.skip = env := rfl

/-- Sequential composition is associative. -/
theorem eval_seq_assoc (env : Env) (s1 s2 s3 : Stmt) :
    evalStmt env (Stmt.seq (Stmt.seq s1 s2) s3) =
    evalStmt env (Stmt.seq s1 (Stmt.seq s2 s3)) := by
  simp [evalStmt]

/-! ## Compositionality as Path Functoriality -/

/-- Semantic path: a path between values induced by evaluating in equal environments. -/
def semanticPath {e1 e2 : Env} (expr : Expr) (h : e1 = e2) :
    Path (evalExpr e1 expr) (evalExpr e2 expr) :=
  Path.congrArg (fun env => evalExpr env expr) (Path.ofEq h)

/-- Semantic path for literals is trivial. -/
theorem semantic_path_lit {e1 e2 : Env} (n : Nat) (h : e1 = e2) :
    (semanticPath (Expr.lit n) h).toEq = congrArg (fun _ => n) h := by
  subst h; rfl

/-- Statement semantic path: paths between output environments. -/
def stmtSemanticPath {e1 e2 : Env} (s : Stmt) (h : e1 = e2) :
    Path (evalStmt e1 s) (evalStmt e2 s) :=
  Path.congrArg (fun env => evalStmt env s) (Path.ofEq h)

/-- Statement path for skip is the environment path. -/
theorem stmt_path_skip {e1 e2 : Env} (h : e1 = e2) :
    (stmtSemanticPath Stmt.skip h).toEq = h := by
  subst h; rfl

/-- Compositionality: seq denotation factors through components. -/
theorem compositionality_seq (env : Env) (s1 s2 : Stmt) :
    evalStmt env (Stmt.seq s1 s2) =
    evalStmt (evalStmt env s1) s2 := rfl

/-! ## Environment Extension Paths -/

/-- Environment extension preserves paths. -/
theorem env_extend_path {e1 e2 : Env} (x : Nat) (v : Nat) (h : e1 = e2) :
    e1.update x v = e2.update x v := by
  subst h; rfl

/-- Path from environment extension. -/
def envExtendPath {e1 e2 : Env} (x : Nat) (v : Nat) (h : e1 = e2) :
    Path (e1.update x v) (e2.update x v) :=
  Path.ofEq (env_extend_path x v h)

/-! ## Substitution Lemma as Path Naturality -/

/-- Simple substitution: replace var x with expression e in expr. -/
def substExpr (x : Nat) (e : Expr) : Expr → Expr
  | Expr.lit n => Expr.lit n
  | Expr.var y => if y == x then e else Expr.var y
  | Expr.add e1 e2 => Expr.add (substExpr x e e1) (substExpr x e e2)
  | Expr.letE y e1 e2 =>
    if y == x then Expr.letE y (substExpr x e e1) e2
    else Expr.letE y (substExpr x e e1) (substExpr x e e2)

/-- Substitution on literal is identity. -/
theorem subst_lit (x : Nat) (e : Expr) (n : Nat) :
    substExpr x e (Expr.lit n) = Expr.lit n := rfl

/-- Substitution on the same variable replaces it. -/
theorem subst_var_same (x : Nat) (e : Expr) :
    substExpr x e (Expr.var x) = e := by simp [substExpr]

/-- Substitution on a different variable leaves it. -/
theorem subst_var_other (x y : Nat) (e : Expr) (h : y != x) :
    substExpr x e (Expr.var y) = Expr.var y := by
  simp [substExpr]
  intro heq
  rw [heq] at h
  simp at h

/-- Substitution distributes over addition. -/
theorem subst_add (x : Nat) (e e1 e2 : Expr) :
    substExpr x e (Expr.add e1 e2) =
    Expr.add (substExpr x e e1) (substExpr x e e2) := rfl

/-! ## Denotational Path Transport -/

/-- Transport of values along semantic paths. -/
def semTransport {e1 e2 : Env} {P : Nat → Type v}
    (expr : Expr) (h : e1 = e2) (val : P (evalExpr e1 expr)) :
    P (evalExpr e2 expr) :=
  Path.transport (semanticPath expr h) val

/-- Transport along reflexive semantic path is identity. -/
theorem sem_transport_refl {P : Nat → Type v}
    (env : Env) (expr : Expr) (val : P (evalExpr env expr)) :
    semTransport expr (rfl : env = env) val = val := by
  simp [semTransport, semanticPath, Path.congrArg, Path.ofEq, Path.transport]

/-! ## Congruence Properties -/

/-- CongrArg for expression evaluation. -/
theorem eval_congrArg (env : Env) {e1 e2 : Expr} (h : e1 = e2) :
    evalExpr env e1 = evalExpr env e2 :=
  _root_.congrArg (evalExpr env) h

/-- Path from expression equality. -/
def exprEqPath (env : Env) {e1 e2 : Expr} (h : e1 = e2) :
    Path (evalExpr env e1) (evalExpr env e2) :=
  Path.ofEq (eval_congrArg env h)

/-- CongrArg for statement evaluation. -/
theorem evalStmt_congrArg (env : Env) {s1 s2 : Stmt} (h : s1 = s2) :
    evalStmt env s1 = evalStmt env s2 :=
  _root_.congrArg (evalStmt env) h

/-- Path from statement equality. -/
def stmtEqPath (env : Env) {s1 s2 : Stmt} (h : s1 = s2) :
    Path (evalStmt env s1) (evalStmt env s2) :=
  Path.ofEq (evalStmt_congrArg env h)

/-! ## Semantic Equivalence -/

/-- Two expressions are semantically equivalent if they produce paths in all environments. -/
def SemEquiv (e1 e2 : Expr) : Prop :=
  ∀ env : Env, evalExpr env e1 = evalExpr env e2

/-- Semantic equivalence is reflexive. -/
theorem semEquiv_refl (e : Expr) : SemEquiv e e :=
  fun _ => rfl

/-- Semantic equivalence is symmetric. -/
theorem semEquiv_symm {e1 e2 : Expr} (h : SemEquiv e1 e2) : SemEquiv e2 e1 :=
  fun env => (h env).symm

/-- Semantic equivalence is transitive. -/
theorem semEquiv_trans {e1 e2 e3 : Expr} (h1 : SemEquiv e1 e2) (h2 : SemEquiv e2 e3) :
    SemEquiv e1 e3 :=
  fun env => (h1 env).trans (h2 env)

/-- Semantic equivalence as a path relation. -/
def semEquivPath {e1 e2 : Expr} (h : SemEquiv e1 e2) (env : Env) :
    Path (evalExpr env e1) (evalExpr env e2) :=
  Path.ofEq (h env)

/-- Add is commutative semantically. -/
theorem add_comm_sem (e1 e2 : Expr) :
    SemEquiv (Expr.add e1 e2) (Expr.add e2 e1) := by
  intro env
  simp [evalExpr, Nat.add_comm]

end DenotationalPaths
end Computation
end Path
end ComputationalPaths
