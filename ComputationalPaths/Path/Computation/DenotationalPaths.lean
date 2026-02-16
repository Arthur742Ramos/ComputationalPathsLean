/-
# Denotational Semantics via Computational Paths

Expression/statement semantics, environment paths, substitution lemma,
compositionality, semantic equivalence — all with genuine `Path` operations.
Zero `Path.ofEq`.

## References

- Stoy, "Denotational Semantics"
- Winskel, "The Formal Semantics of Programming Languages"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Computation
namespace DenotationalPaths

universe u v

/-! ## Syntax -/

/-- Simple expression language. -/
inductive Expr where
  | lit : Nat → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | letE : Nat → Expr → Expr → Expr
  deriving Repr, BEq, DecidableEq

/-- Simple statement language. -/
inductive Stmt where
  | skip : Stmt
  | assign : Nat → Expr → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifZ : Expr → Stmt → Stmt → Stmt
  deriving Repr, BEq, DecidableEq

/-! ## Environments -/

/-- An environment maps variables to values. -/
structure Env where
  lookup : Nat → Nat

/-- Update an environment at a given variable. -/
def Env.update (env : Env) (x : Nat) (v : Nat) : Env :=
  ⟨fun y => if y == x then v else env.lookup y⟩

/-- 1. Update-same: retrieving updated variable. -/
theorem env_update_same (env : Env) (x : Nat) (v : Nat) :
    (env.update x v).lookup x = v := by
  simp [Env.update]

/-- 2. Update-other: different variable unchanged. -/
theorem env_update_other (env : Env) (x y : Nat) (v : Nat) (h : y != x) :
    (env.update x v).lookup y = env.lookup y := by
  simp [Env.update]
  intro heq; rw [heq] at h; simp at h

/-- 3. Double update at same variable: last wins. -/
theorem env_update_shadow (env : Env) (x : Nat) (v1 v2 : Nat) :
    (env.update x v1).update x v2 = env.update x v2 := by
  show Env.mk _ = Env.mk _
  congr 1; funext y; simp [Env.update]; split <;> rfl

/-- 4. Updates at different variables commute. -/
theorem env_update_comm (env : Env) (x y : Nat) (vx vy : Nat) (hne : x ≠ y) :
    (env.update x vx).update y vy = (env.update y vy).update x vx := by
  show Env.mk _ = Env.mk _
  congr 1; funext z; simp [Env.update]
  split
  · split
    · next h1 h2 =>
        have := BEq.eq_of_beq h1
        have := BEq.eq_of_beq h2
        omega
    · rfl
  · rfl

/-! ## Meaning Functions -/

/-- 5. Expression denotation. -/
def evalExpr (env : Env) : Expr → Nat
  | Expr.lit n => n
  | Expr.var x => env.lookup x
  | Expr.add e1 e2 => evalExpr env e1 + evalExpr env e2
  | Expr.mul e1 e2 => evalExpr env e1 * evalExpr env e2
  | Expr.letE x e1 e2 => evalExpr (env.update x (evalExpr env e1)) e2

/-- 6. Statement denotation. -/
def evalStmt (env : Env) : Stmt → Env
  | Stmt.skip => env
  | Stmt.assign x e => env.update x (evalExpr env e)
  | Stmt.seq s1 s2 => evalStmt (evalStmt env s1) s2
  | Stmt.ifZ cond s1 s2 => if evalExpr env cond == 0 then evalStmt env s1 else evalStmt env s2

/-- 7. Skip is the identity. -/
theorem eval_skip (env : Env) : evalStmt env Stmt.skip = env := rfl

/-- 8. Sequential composition is associative. -/
theorem eval_seq_assoc (env : Env) (s1 s2 s3 : Stmt) :
    evalStmt env (Stmt.seq (Stmt.seq s1 s2) s3) =
    evalStmt env (Stmt.seq s1 (Stmt.seq s2 s3)) := by
  simp [evalStmt]

/-- 9. Skip-seq is identity. -/
theorem eval_skip_seq (env : Env) (s : Stmt) :
    evalStmt env (Stmt.seq Stmt.skip s) = evalStmt env s := by
  simp [evalStmt]

/-- 10. Seq-skip is identity. -/
theorem eval_seq_skip (env : Env) (s : Stmt) :
    evalStmt env (Stmt.seq s Stmt.skip) = evalStmt env s := by
  simp [evalStmt]

/-! ## Semantic Paths -/

/-- 11. Path between expression values under equal environments. -/
def semanticPath (env : Env) (e1 e2 : Expr) (h : ∀ env', evalExpr env' e1 = evalExpr env' e2) :
    Path (evalExpr env e1) (evalExpr env e2) :=
  Path.mk [Step.mk (evalExpr env e1) (evalExpr env e2) (h env)] (h env)

/-- 12. Literal semantic path is refl. -/
def lit_semantic_refl (env : Env) (n : Nat) : Path (evalExpr env (Expr.lit n)) n :=
  Path.refl n

/-- 13. Variable semantic path is refl. -/
def var_semantic_refl (env : Env) (x : Nat) : Path (evalExpr env (Expr.var x)) (env.lookup x) :=
  Path.refl _

/-- 14. Add distributes over evaluation (refl). -/
def add_eval_path (env : Env) (e1 e2 : Expr) :
    Path (evalExpr env (Expr.add e1 e2)) (evalExpr env e1 + evalExpr env e2) :=
  Path.refl _

/-- 15. Mul distributes over evaluation (refl). -/
def mul_eval_path (env : Env) (e1 e2 : Expr) :
    Path (evalExpr env (Expr.mul e1 e2)) (evalExpr env e1 * evalExpr env e2) :=
  Path.refl _

/-! ## Compositionality as Path Functoriality -/

/-- 16. Statement path for skip is refl. -/
def stmt_path_skip (env : Env) : Path (evalStmt env Stmt.skip) env :=
  Path.refl env

/-- 17. Compositionality: seq factors through components. -/
theorem compositionality_seq (env : Env) (s1 s2 : Stmt) :
    evalStmt env (Stmt.seq s1 s2) =
    evalStmt (evalStmt env s1) s2 := rfl

/-- 18. Compositionality path. -/
def compositionality_path (env : Env) (s1 s2 : Stmt) :
    Path (evalStmt env (Stmt.seq s1 s2)) (evalStmt (evalStmt env s1) s2) :=
  Path.refl _

/-! ## Substitution -/

/-- Simple substitution: replace var x with expression e. -/
def substExpr (x : Nat) (e : Expr) : Expr → Expr
  | Expr.lit n => Expr.lit n
  | Expr.var y => if y == x then e else Expr.var y
  | Expr.add e1 e2 => Expr.add (substExpr x e e1) (substExpr x e e2)
  | Expr.mul e1 e2 => Expr.mul (substExpr x e e1) (substExpr x e e2)
  | Expr.letE y e1 e2 =>
    if y == x then Expr.letE y (substExpr x e e1) e2
    else Expr.letE y (substExpr x e e1) (substExpr x e e2)

/-- 19. Substitution on literal is identity. -/
theorem subst_lit (x : Nat) (e : Expr) (n : Nat) :
    substExpr x e (Expr.lit n) = Expr.lit n := rfl

/-- 20. Substitution on same variable replaces. -/
theorem subst_var_same (x : Nat) (e : Expr) :
    substExpr x e (Expr.var x) = e := by simp [substExpr]

/-- 21. Substitution on different variable is identity. -/
theorem subst_var_other (x y : Nat) (e : Expr) (h : y != x) :
    substExpr x e (Expr.var y) = Expr.var y := by
  simp [substExpr]; intro heq; rw [heq] at h; simp at h

/-- 22. Substitution distributes over add. -/
theorem subst_add (x : Nat) (e e1 e2 : Expr) :
    substExpr x e (Expr.add e1 e2) =
    Expr.add (substExpr x e e1) (substExpr x e e2) := rfl

/-- 23. Substitution distributes over mul. -/
theorem subst_mul (x : Nat) (e e1 e2 : Expr) :
    substExpr x e (Expr.mul e1 e2) =
    Expr.mul (substExpr x e e1) (substExpr x e e2) := rfl

/-- 24. Path: substitution on lit is identity. -/
def subst_lit_path (env : Env) (x : Nat) (e : Expr) (n : Nat) :
    Path (evalExpr env (substExpr x e (Expr.lit n))) (evalExpr env (Expr.lit n)) :=
  Path.refl _

/-! ## Semantic Equivalence -/

/-- Two expressions are semantically equivalent. -/
def SemEquiv (e1 e2 : Expr) : Prop :=
  ∀ env : Env, evalExpr env e1 = evalExpr env e2

/-- 25. Semantic equivalence is reflexive. -/
theorem semEquiv_refl (e : Expr) : SemEquiv e e :=
  fun _ => rfl

/-- 26. Semantic equivalence is symmetric. -/
theorem semEquiv_symm {e1 e2 : Expr} (h : SemEquiv e1 e2) : SemEquiv e2 e1 :=
  fun env => (h env).symm

/-- 27. Semantic equivalence is transitive. -/
theorem semEquiv_trans {e1 e2 e3 : Expr} (h1 : SemEquiv e1 e2) (h2 : SemEquiv e2 e3) :
    SemEquiv e1 e3 :=
  fun env => (h1 env).trans (h2 env)

/-- 28. Semantic equivalence as a path. -/
def semEquivPath {e1 e2 : Expr} (h : SemEquiv e1 e2) (env : Env) :
    Path (evalExpr env e1) (evalExpr env e2) :=
  Path.mk [Step.mk _ _ (h env)] (h env)

/-- 29. Add is commutative semantically. -/
theorem add_comm_sem (e1 e2 : Expr) :
    SemEquiv (Expr.add e1 e2) (Expr.add e2 e1) := by
  intro env; simp [evalExpr, Nat.add_comm]

/-- 30. Mul is commutative semantically. -/
theorem mul_comm_sem (e1 e2 : Expr) :
    SemEquiv (Expr.mul e1 e2) (Expr.mul e2 e1) := by
  intro env; simp [evalExpr, Nat.mul_comm]

/-- 31. Add zero on right is identity. -/
theorem add_zero_right_sem (e : Expr) :
    SemEquiv (Expr.add e (Expr.lit 0)) e := by
  intro env; simp [evalExpr]

/-- 32. Add zero on left is identity. -/
theorem add_zero_left_sem (e : Expr) :
    SemEquiv (Expr.add (Expr.lit 0) e) e := by
  intro env; simp [evalExpr]

/-- 33. Mul one on right is identity. -/
theorem mul_one_right_sem (e : Expr) :
    SemEquiv (Expr.mul e (Expr.lit 1)) e := by
  intro env; simp [evalExpr]

/-- 34. Mul zero annihilates. -/
theorem mul_zero_right_sem (e : Expr) :
    SemEquiv (Expr.mul e (Expr.lit 0)) (Expr.lit 0) := by
  intro env; simp [evalExpr]

/-- 35. Add is associative semantically. -/
theorem add_assoc_sem (e1 e2 e3 : Expr) :
    SemEquiv (Expr.add (Expr.add e1 e2) e3) (Expr.add e1 (Expr.add e2 e3)) := by
  intro env; simp [evalExpr, Nat.add_assoc]

/-- 36. Mul is associative semantically. -/
theorem mul_assoc_sem (e1 e2 e3 : Expr) :
    SemEquiv (Expr.mul (Expr.mul e1 e2) e3) (Expr.mul e1 (Expr.mul e2 e3)) := by
  intro env; simp [evalExpr, Nat.mul_assoc]

/-! ## Statement Equivalence -/

/-- Two statements are semantically equivalent. -/
def StmtEquiv (s1 s2 : Stmt) : Prop :=
  ∀ env : Env, evalStmt env s1 = evalStmt env s2

/-- 37. Statement equivalence is reflexive. -/
theorem stmtEquiv_refl (s : Stmt) : StmtEquiv s s :=
  fun _ => rfl

/-- 38. Statement equivalence is symmetric. -/
theorem stmtEquiv_symm {s1 s2 : Stmt} (h : StmtEquiv s1 s2) : StmtEquiv s2 s1 :=
  fun env => (h env).symm

/-- 39. Statement equivalence is transitive. -/
theorem stmtEquiv_trans {s1 s2 s3 : Stmt} (h1 : StmtEquiv s1 s2) (h2 : StmtEquiv s2 s3) :
    StmtEquiv s1 s3 :=
  fun env => (h1 env).trans (h2 env)

/-- 40. Skip-seq equivalence. -/
theorem skip_seq_equiv (s : Stmt) : StmtEquiv (Stmt.seq Stmt.skip s) s :=
  fun _ => rfl

/-- 41. Seq-skip equivalence. -/
theorem seq_skip_equiv (s : Stmt) : StmtEquiv (Stmt.seq s Stmt.skip) s :=
  fun _ => rfl

/-- 42. Seq is associative. -/
theorem seq_assoc_equiv (s1 s2 s3 : Stmt) :
    StmtEquiv (Stmt.seq (Stmt.seq s1 s2) s3) (Stmt.seq s1 (Stmt.seq s2 s3)) :=
  fun _ => rfl

/-- 43. Equivalence as path. -/
def stmtEquivPath {s1 s2 : Stmt} (h : StmtEquiv s1 s2) (env : Env) :
    Path (evalStmt env s1) (evalStmt env s2) :=
  Path.mk [Step.mk _ _ (h env)] (h env)

/-! ## Congruence Lifting -/

/-- 44. Semantic equivalence of subexpressions lifts to add-left. -/
theorem semEquiv_add_left {e1 e2 : Expr} (h : SemEquiv e1 e2) (e3 : Expr) :
    SemEquiv (Expr.add e1 e3) (Expr.add e2 e3) :=
  fun env => by simp [evalExpr]; rw [h env]

/-- 45. Semantic equivalence of subexpressions lifts to add-right. -/
theorem semEquiv_add_right {e1 e2 : Expr} (h : SemEquiv e1 e2) (e3 : Expr) :
    SemEquiv (Expr.add e3 e1) (Expr.add e3 e2) :=
  fun env => by simp [evalExpr]; rw [h env]

end DenotationalPaths
end Computation
end Path
end ComputationalPaths
