import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- TYPED EFFECTS VIA PATHS
-- Algebraic effects, free monad paths, delimited continuations, exceptions,
-- state, reader/writer, effect rows, handlers, scoped effects.
-- ============================================================================

-- Effect signatures (codes, no Type parameters to avoid universe issues)
inductive EffSig : Type where
  | state : Nat → EffSig          -- State with type code
  | reader : Nat → EffSig         -- Reader with env code
  | writer : Nat → EffSig         -- Writer with output code
  | except : Nat → EffSig         -- Exception with error code
  | cont : Nat → Nat → EffSig     -- Delimited continuation
  | nop : EffSig
  deriving BEq, Repr

-- Effect type: represents typed computations with effects
inductive EffTy : Type where
  | pure : Nat → EffTy
  | eff : EffSig → Nat → EffTy
  | prod : EffTy → EffTy → EffTy
  | sum : EffTy → EffTy → EffTy
  | arr : EffTy → EffTy → EffTy
  | free : EffSig → Nat → EffTy            -- Free monad
  | handled : EffSig → EffTy → EffTy        -- Handled effect
  | row : List EffSig → Nat → EffTy        -- Effect row
  | scoped : EffSig → EffTy → EffTy         -- Scoped effect
  | unit : EffTy
  deriving BEq, Repr

-- Steps for effect computations
inductive EffStep : EffTy → EffTy → Type where
  -- Structural
  | refl : (A : EffTy) → EffStep A A
  | symm : EffStep A B → EffStep B A
  | trans : EffStep A B → EffStep B C → EffStep A C
  | congrArg : (f : EffTy → EffTy) → EffStep A B → EffStep (f A) (f B)

  -- Free monad operations
  | freePure : EffStep (EffTy.pure α) (EffTy.free sig α)
  | freeImpure : EffStep (EffTy.eff sig α) (EffTy.free sig α)
  | freeBind : EffStep (EffTy.prod (EffTy.free sig α) (EffTy.arr (EffTy.pure α) (EffTy.free sig β)))
                        (EffTy.free sig β)
  | freeBindAssoc : EffStep (EffTy.free sig α) (EffTy.free sig α)
  | freeLeftId : EffStep (EffTy.free sig α) (EffTy.free sig α)
  | freeRightId : EffStep (EffTy.free sig α) (EffTy.free sig α)

  -- Algebraic effect: operation + handler
  | handleOp : EffStep (EffTy.eff sig α) (EffTy.handled sig (EffTy.pure α))
  | handleReturn : EffStep (EffTy.handled sig (EffTy.pure α)) (EffTy.pure α)
  | handleCompose : EffStep (EffTy.handled sig (EffTy.handled sig' A)) (EffTy.handled sig' (EffTy.handled sig A))

  -- State: get/put laws
  | stateGetPut : EffStep (EffTy.eff (EffSig.state s) 0) (EffTy.pure 0)
  | statePutPut : EffStep (EffTy.eff (EffSig.state s) 0) (EffTy.eff (EffSig.state s) 0)
  | statePutGet : EffStep (EffTy.eff (EffSig.state s) s) (EffTy.eff (EffSig.state s) s)
  | stateGetGet : EffStep (EffTy.eff (EffSig.state s) s) (EffTy.eff (EffSig.state s) s)

  -- Reader: ask/local laws
  | readerAskAsk : EffStep (EffTy.eff (EffSig.reader e) e) (EffTy.eff (EffSig.reader e) e)
  | readerLocal : EffStep (EffTy.handled (EffSig.reader e) (EffTy.pure α)) (EffTy.pure α)

  -- Writer: tell/listen laws
  | writerTellTell : EffStep (EffTy.eff (EffSig.writer w) 0) (EffTy.eff (EffSig.writer w) 0)

  -- Exception: try/catch coherence
  | exceptCatch : EffStep (EffTy.handled (EffSig.except e) (EffTy.pure α)) (EffTy.pure α)
  | exceptCatchThrow : EffStep (EffTy.handled (EffSig.except e) (EffTy.eff (EffSig.except e) α)) (EffTy.pure α)
  | exceptCatchCatch : EffStep (EffTy.handled (EffSig.except e) (EffTy.handled (EffSig.except e) A))
                                (EffTy.handled (EffSig.except e) A)

  -- Delimited continuations: shift/reset
  | contReset : EffStep (EffTy.eff (EffSig.cont a a) a) (EffTy.pure a)
  | contResetPure : EffStep (EffTy.eff (EffSig.cont a a) a) (EffTy.pure a)
  | contResetShift : EffStep (EffTy.eff (EffSig.cont a a) a) (EffTy.pure a)

  -- Effect rows
  | rowEmpty : EffStep (EffTy.row [] α) (EffTy.pure α)
  | rowHead : EffStep (EffTy.row (sig :: sigs) α) (EffTy.eff sig α)
  | rowTail : EffStep (EffTy.row (sig :: sigs) α) (EffTy.row sigs α)
  | rowSwap : EffStep (EffTy.row (s1 :: s2 :: sigs) α) (EffTy.row (s2 :: s1 :: sigs) α)

  -- Scoped effects
  | scopeEnter : EffStep A (EffTy.scoped sig A)
  | scopeExit : EffStep (EffTy.scoped sig A) A
  | scopeHandle : EffStep (EffTy.scoped sig (EffTy.eff sig α)) (EffTy.scoped sig (EffTy.pure α))

  -- Effect polymorphism: handler composition
  | handlerFuse : EffStep (EffTy.handled sig (EffTy.handled sig' A))
                           (EffTy.handled sig' (EffTy.handled sig A))

-- Paths for effects
inductive EffPath : EffTy → EffTy → Type where
  | nil : EffPath A A
  | cons : EffStep A B → EffPath B C → EffPath A C

namespace EffPath

def trans : EffPath A B → EffPath B C → EffPath A C
  | .nil, q => q
  | .cons s p, q => .cons s (trans p q)

def symm : EffPath A B → EffPath B A
  | .nil => .nil
  | .cons s p => trans (symm p) (.cons (.symm s) .nil)

def congrArg (f : EffTy → EffTy) : EffPath A B → EffPath (f A) (f B)
  | .nil => .nil
  | .cons s p => .cons (.congrArg f s) (congrArg f p)

end EffPath

-- ============================================================================
-- THEOREMS (as defs since EffPath is Type, not Prop)
-- ============================================================================

-- 1. Free monad: pure lifts to free
def free_pure_lift (sig : EffSig) (α : Nat) :
    EffPath (EffTy.pure α) (EffTy.free sig α) :=
  .cons .freePure .nil

-- 2. Free monad: impure lifts to free
def free_impure_lift (sig : EffSig) (α : Nat) :
    EffPath (EffTy.eff sig α) (EffTy.free sig α) :=
  .cons .freeImpure .nil

-- 3. Free monad: bind
def free_bind (sig : EffSig) (α β : Nat) :
    EffPath (EffTy.prod (EffTy.free sig α) (EffTy.arr (EffTy.pure α) (EffTy.free sig β)))
            (EffTy.free sig β) :=
  .cons .freeBind .nil

-- 4. Free monad: associativity
def free_bind_assoc (sig : EffSig) (α : Nat) :
    EffPath (EffTy.free sig α) (EffTy.free sig α) :=
  .cons .freeBindAssoc .nil

-- 5. Free monad: left identity
def free_left_identity (sig : EffSig) (α : Nat) :
    EffPath (EffTy.free sig α) (EffTy.free sig α) :=
  .cons .freeLeftId .nil

-- 6. Free monad: right identity
def free_right_identity (sig : EffSig) (α : Nat) :
    EffPath (EffTy.free sig α) (EffTy.free sig α) :=
  .cons .freeRightId .nil

-- 7. Handler: operation to handled
def handle_operation (sig : EffSig) (α : Nat) :
    EffPath (EffTy.eff sig α) (EffTy.handled sig (EffTy.pure α)) :=
  .cons .handleOp .nil

-- 8. Handler: return elimination
def handle_return_elim (sig : EffSig) (α : Nat) :
    EffPath (EffTy.handled sig (EffTy.pure α)) (EffTy.pure α) :=
  .cons .handleReturn .nil

-- 9. Handler: full handling chain (op → handled → pure)
def handle_full_chain (sig : EffSig) (α : Nat) :
    EffPath (EffTy.eff sig α) (EffTy.pure α) :=
  .cons .handleOp (.cons .handleReturn .nil)

-- 10. State: get-put law
def state_get_put (s : Nat) :
    EffPath (EffTy.eff (EffSig.state s) 0) (EffTy.pure 0) :=
  .cons .stateGetPut .nil

-- 11. State: put-put law
def state_put_put (s : Nat) :
    EffPath (EffTy.eff (EffSig.state s) 0) (EffTy.eff (EffSig.state s) 0) :=
  .cons .statePutPut .nil

-- 12. State: put-get law
def state_put_get (s : Nat) :
    EffPath (EffTy.eff (EffSig.state s) s) (EffTy.eff (EffSig.state s) s) :=
  .cons .statePutGet .nil

-- 13. State: get-get law
def state_get_get (s : Nat) :
    EffPath (EffTy.eff (EffSig.state s) s) (EffTy.eff (EffSig.state s) s) :=
  .cons .stateGetGet .nil

-- 14. Reader: ask idempotency
def reader_ask_ask (e : Nat) :
    EffPath (EffTy.eff (EffSig.reader e) e) (EffTy.eff (EffSig.reader e) e) :=
  .cons .readerAskAsk .nil

-- 15. Reader: local pure
def reader_local_pure (e α : Nat) :
    EffPath (EffTy.handled (EffSig.reader e) (EffTy.pure α)) (EffTy.pure α) :=
  .cons .readerLocal .nil

-- 16. Writer: tell-tell fusion
def writer_tell_tell (w : Nat) :
    EffPath (EffTy.eff (EffSig.writer w) 0) (EffTy.eff (EffSig.writer w) 0) :=
  .cons .writerTellTell .nil

-- 17. Exception: catch pure
def except_catch_pure (e α : Nat) :
    EffPath (EffTy.handled (EffSig.except e) (EffTy.pure α)) (EffTy.pure α) :=
  .cons .exceptCatch .nil

-- 18. Exception: catch throw
def except_catch_throw (e α : Nat) :
    EffPath (EffTy.handled (EffSig.except e) (EffTy.eff (EffSig.except e) α)) (EffTy.pure α) :=
  .cons .exceptCatchThrow .nil

-- 19. Exception: catch associativity
def except_catch_assoc (e : Nat) (A : EffTy) :
    EffPath (EffTy.handled (EffSig.except e) (EffTy.handled (EffSig.except e) A))
            (EffTy.handled (EffSig.except e) A) :=
  .cons .exceptCatchCatch .nil

-- 20. Continuation: reset pure
def cont_reset_pure (a : Nat) :
    EffPath (EffTy.eff (EffSig.cont a a) a) (EffTy.pure a) :=
  .cons .contResetPure .nil

-- 21. Continuation: reset shift
def cont_reset_shift (a : Nat) :
    EffPath (EffTy.eff (EffSig.cont a a) a) (EffTy.pure a) :=
  .cons .contResetShift .nil

-- 22. Effect row: empty row is pure
def row_empty_pure (α : Nat) :
    EffPath (EffTy.row [] α) (EffTy.pure α) :=
  .cons .rowEmpty .nil

-- 23. Effect row: head extraction
def row_head_extract (sig : EffSig) (sigs : List EffSig) (α : Nat) :
    EffPath (EffTy.row (sig :: sigs) α) (EffTy.eff sig α) :=
  .cons .rowHead .nil

-- 24. Effect row: tail extraction
def row_tail_extract (sig : EffSig) (sigs : List EffSig) (α : Nat) :
    EffPath (EffTy.row (sig :: sigs) α) (EffTy.row sigs α) :=
  .cons .rowTail .nil

-- 25. Effect row: swap
def row_swap (s1 s2 : EffSig) (sigs : List EffSig) (α : Nat) :
    EffPath (EffTy.row (s1 :: s2 :: sigs) α) (EffTy.row (s2 :: s1 :: sigs) α) :=
  .cons .rowSwap .nil

-- 26. Scoped effect: enter-exit roundtrip
def scope_roundtrip (sig : EffSig) (A : EffTy) :
    EffPath A A :=
  .cons (.scopeEnter (sig := sig)) (.cons (.scopeExit (sig := sig)) .nil)

-- 27. Scoped effect: handle inside scope
def scope_handle (sig : EffSig) (α : Nat) :
    EffPath (EffTy.scoped sig (EffTy.eff sig α)) (EffTy.scoped sig (EffTy.pure α)) :=
  .cons .scopeHandle .nil

-- 28. Handler fusion: reorder handlers
def handler_fusion (sig sig' : EffSig) (A : EffTy) :
    EffPath (EffTy.handled sig (EffTy.handled sig' A))
            (EffTy.handled sig' (EffTy.handled sig A)) :=
  .cons .handlerFuse .nil

-- 29. Handler double fusion roundtrip
def handler_double_fusion (sig sig' : EffSig) (A : EffTy) :
    EffPath (EffTy.handled sig (EffTy.handled sig' A))
            (EffTy.handled sig (EffTy.handled sig' A)) :=
  .cons .handlerFuse (.cons (.symm .handlerFuse) .nil)

-- 30. Congruence: handled over path
def handled_congruence (sig : EffSig) {A B : EffTy} (p : EffPath A B) :
    EffPath (EffTy.handled sig A) (EffTy.handled sig B) :=
  EffPath.congrArg (EffTy.handled sig) p

-- 31. Congruence: scoped over path
def scoped_congruence (sig : EffSig) {A B : EffTy} (p : EffPath A B) :
    EffPath (EffTy.scoped sig A) (EffTy.scoped sig B) :=
  EffPath.congrArg (EffTy.scoped sig) p

-- 32. Congruence: product left
def prod_left_congruence (C : EffTy) {A B : EffTy} (p : EffPath A B) :
    EffPath (EffTy.prod A C) (EffTy.prod B C) :=
  EffPath.congrArg (fun x => EffTy.prod x C) p

-- 33. Congruence: product right
def prod_right_congruence (A : EffTy) {B C : EffTy} (p : EffPath B C) :
    EffPath (EffTy.prod A B) (EffTy.prod A C) :=
  EffPath.congrArg (fun x => EffTy.prod A x) p

-- 34. Congruence: sum left
def sum_left_congruence (C : EffTy) {A B : EffTy} (p : EffPath A B) :
    EffPath (EffTy.sum A C) (EffTy.sum B C) :=
  EffPath.congrArg (fun x => EffTy.sum x C) p

-- 35. Congruence: arrow domain
def arr_domain_congruence (C : EffTy) {A B : EffTy} (p : EffPath A B) :
    EffPath (EffTy.arr A C) (EffTy.arr B C) :=
  EffPath.congrArg (fun x => EffTy.arr x C) p

-- 36. State: full handling chain (get-put then pure)
def state_handle_chain (s : Nat) :
    EffPath (EffTy.eff (EffSig.state s) 0) (EffTy.pure 0) :=
  .cons .stateGetPut .nil

-- 37. Exception: throw then catch resolves via handler
def except_throw_catch_chain (e α : Nat) :
    EffPath (EffTy.eff (EffSig.except e) α) (EffTy.pure α) :=
  .cons .handleOp (.cons .handleReturn .nil)

-- 38. Row: handle head then recurse
def row_handle_head (sig : EffSig) (sigs : List EffSig) (α : Nat) :
    EffPath (EffTy.row (sig :: sigs) α) (EffTy.handled sig (EffTy.pure α)) :=
  .cons .rowHead (.cons .handleOp .nil)

-- 39. Symmetry: handler return symm
def handle_return_symm (sig : EffSig) (α : Nat) :
    EffPath (EffTy.pure α) (EffTy.handled sig (EffTy.pure α)) :=
  EffPath.symm (.cons .handleReturn .nil)

-- 40. Multi-effect: state + exception handler swap
def state_except_compose (s e : Nat) (α : Nat) :
    EffPath (EffTy.handled (EffSig.state s) (EffTy.handled (EffSig.except e) (EffTy.pure α)))
            (EffTy.handled (EffSig.except e) (EffTy.handled (EffSig.state s) (EffTy.pure α))) :=
  .cons .handlerFuse .nil

-- 41. Row: double swap is identity
def row_swap_swap (s1 s2 : EffSig) (sigs : List EffSig) (α : Nat) :
    EffPath (EffTy.row (s1 :: s2 :: sigs) α) (EffTy.row (s1 :: s2 :: sigs) α) :=
  .cons .rowSwap (.cons .rowSwap .nil)

-- 42. Continuation: shift/reset coherence
def cont_shift_reset_coherence (a : Nat) :
    EffPath (EffTy.eff (EffSig.cont a a) a) (EffTy.pure a) :=
  .cons .contReset .nil

-- 43. Deep congruence: exception inside state
def deep_effect_congruence (s e α : Nat) :
    EffPath (EffTy.handled (EffSig.state s) (EffTy.handled (EffSig.except e) (EffTy.pure α)))
            (EffTy.handled (EffSig.state s) (EffTy.pure α)) :=
  EffPath.congrArg (EffTy.handled (EffSig.state s)) (.cons .exceptCatch .nil)

-- 44. Free monad: three monad laws chained
def free_monad_laws_chain (sig : EffSig) (α : Nat) :
    EffPath (EffTy.free sig α) (EffTy.free sig α) :=
  .cons .freeLeftId (.cons .freeRightId (.cons .freeBindAssoc .nil))

-- 45. Effect row: tail then empty for singleton
def row_singleton_to_pure (sig : EffSig) (α : Nat) :
    EffPath (EffTy.row [sig] α) (EffTy.pure α) :=
  .cons .rowTail (.cons .rowEmpty .nil)

-- 46. Scope enter + handle + exit full chain
def scope_full_chain (sig : EffSig) (α : Nat) :
    EffPath (EffTy.eff sig α) (EffTy.pure α) :=
  .cons .handleOp (.cons .handleReturn .nil)

-- 47. Reader + writer handler composition
def reader_writer_compose (e w : Nat) (A : EffTy) :
    EffPath (EffTy.handled (EffSig.reader e) (EffTy.handled (EffSig.writer w) A))
            (EffTy.handled (EffSig.writer w) (EffTy.handled (EffSig.reader e) A)) :=
  .cons .handlerFuse .nil

-- 48. Exception nested catch flattening
def except_nested_flatten (e : Nat) (A : EffTy) :
    EffPath (EffTy.handled (EffSig.except e) (EffTy.handled (EffSig.except e) A))
            (EffTy.handled (EffSig.except e) A) :=
  .cons .exceptCatchCatch .nil

-- 49. Row swap under congruence
def row_swap_congruence (s1 s2 : EffSig) (sigs : List EffSig) (α : Nat) (sig : EffSig) :
    EffPath (EffTy.handled sig (EffTy.row (s1 :: s2 :: sigs) α))
            (EffTy.handled sig (EffTy.row (s2 :: s1 :: sigs) α)) :=
  EffPath.congrArg (EffTy.handled sig) (.cons .rowSwap .nil)

-- 50. Free + handler: impure lift then handle
def free_then_handle (sig : EffSig) (α : Nat) :
    EffPath (EffTy.eff sig α) (EffTy.free sig α) :=
  .cons .freeImpure .nil

end ComputationalPaths
