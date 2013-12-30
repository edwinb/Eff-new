module Effects

import Language.Reflection
import Control.Catchable

%access public

---- Effects

Effect : Type
Effect = (x : Type) -> Type -> (x -> Type) -> Type

data EFFECT : Type where
     MkEff : Type -> Effect -> EFFECT

class Handler (e : Effect) (m : Type -> Type) where
     handle : res -> (eff : e t res resk) -> 
              ((x : t) -> resk x -> m a) -> m a

---- Properties and proof construction

using (xs : List a, ys : List a)
  data SubList : List a -> List a -> Type where
       SubNil : SubList {a} [] []
       Keep   : SubList xs ys -> SubList (x :: xs) (x :: ys)
       Drop   : SubList xs ys -> SubList xs (x :: ys)

  subListId : SubList xs xs
  subListId {xs = Nil} = SubNil
  subListId {xs = x :: xs} = Keep subListId

data Env  : (m : Type -> Type) -> List EFFECT -> Type where
     Nil  : Env m Nil
     (::) : Handler eff m => a -> Env m xs -> Env m (MkEff a eff :: xs)

data EffElem : Effect -> Type ->
               List EFFECT -> Type where
     Here : EffElem x a (MkEff a x :: xs)
     There : EffElem x a xs -> EffElem x a (y :: xs)

-- make an environment corresponding to a sub-list
dropEnv : Env m ys -> SubList xs ys -> Env m xs
dropEnv [] SubNil = []
dropEnv (v :: vs) (Keep rest) = v :: dropEnv vs rest
dropEnv (v :: vs) (Drop rest) = dropEnv vs rest

updateWith : (ys' : List a) -> (xs : List a) ->
             SubList ys xs -> List a
updateWith (y :: ys) (x :: xs) (Keep rest) = y :: updateWith ys xs rest
updateWith ys        (x :: xs) (Drop rest) = x :: updateWith ys xs rest
updateWith []        []        SubNil      = []
updateWith (y :: ys) []        SubNil      = y :: ys
updateWith []        (x :: xs) (Keep rest) = []

-- put things back, replacing old with new in the sub-environment
rebuildEnv : Env m ys' -> (prf : SubList ys xs) ->
             Env m xs -> Env m (updateWith ys' xs prf)
rebuildEnv []        SubNil      env = env
rebuildEnv (x :: xs) (Keep rest) (y :: env) = x :: rebuildEnv xs rest env
rebuildEnv xs        (Drop rest) (y :: env) = y :: rebuildEnv xs rest env
rebuildEnv (x :: xs) SubNil      [] = x :: xs

---- The Effect EDSL itself ----

-- some proof automation

%reflection
reflectListEffElem : List a -> Tactic
reflectListEffElem [] = Refine "Here" `Seq` Solve
reflectListEffElem (x :: xs)
     = Try (Refine "Here" `Seq` Solve)
           (Refine "There" `Seq` (Solve `Seq` reflectListEffElem xs))
-- TMP HACK! FIXME!
-- The evaluator needs a 'function case' to know its a reflection function
-- until we propagate that information! Without this, the _ case won't get
-- matched. 
reflectListEffElem (x ++ y) = Refine "Here" `Seq` Solve
reflectListEffElem _ = Refine "Here" `Seq` Solve

%reflection
reflectSubList : List a -> Tactic
reflectSubList [] = Refine "SubNil" `Seq` Solve
reflectSubList (x :: xs)
     = Try (Refine "subListId" `Seq` Solve)
           (Try (Refine "Keep" `Seq` (Solve `Seq` reflectSubList xs))
                (Refine "Drop" `Seq` (Solve `Seq` reflectSubList xs)))
reflectSubList (x ++ y) = Refine "subListId" `Seq` Solve
reflectSubList _ = Refine "subListId" `Seq` Solve

%reflection
reflectEff : (P : Type) -> Tactic
reflectEff (EffElem m a xs)
     = reflectListEffElem xs `Seq` Solve
reflectEff (SubList xs ys)
     = reflectSubList ys `Seq` Solve

updateResTy : (val : t) ->
              (xs : List EFFECT) -> EffElem e a xs -> e t a b ->
              List EFFECT
updateResTy {b} val (MkEff a e :: xs) Here n = (MkEff (b val) e) :: xs
updateResTy     val (x :: xs)    (There p) n = x :: updateResTy val xs p n

-- updateResTyImm : (xs : List EFFECT) -> EffElem e a xs -> Type ->
--                  List EFFECT
-- updateResTyImm (MkEff a e :: xs) Here b = (MkEff b e) :: xs
-- updateResTyImm (x :: xs)    (There p) b = x :: updateResTyImm xs p b

infix 5 :::, :-, :=

data LRes : lbl -> Type -> Type where
     (:=) : (x : lbl) -> res -> LRes x res

(:::) : lbl -> EFFECT -> EFFECT
(:::) {lbl} x (MkEff r e) = MkEff (LRes x r) e

private
unlabel : {l : ty} -> Env m [l ::: x] -> Env m [x]
unlabel {m} {x = MkEff a eff} [l := v] = [v]

private
relabel : (l : ty) -> Env m xs -> Env m (map (\x => l ::: x) xs)
relabel {xs = []} l [] = []
relabel {xs = (MkEff a e :: xs)} l (v :: vs) = (l := v) :: relabel l vs

-- the language of Effects

data EffM : (m : Type -> Type) ->
            (x : Type) ->
            List EFFECT -> (x -> List EFFECT) -> Type where
     value   : a -> EffM m a xs (\v => xs)
     (>>=)   : EffM m a xs xs' -> 
               ((val : a) -> EffM m b (xs' val) xs'') -> EffM m b xs xs''
     effect  : (prf : EffElem e a xs) ->
               (eff : e t a b) ->
               EffM m t xs (\v => updateResTy v xs prf eff)

     lift    : (prf : SubList ys xs) ->
               EffM m t ys ys' -> EffM m t xs (\v => updateWith (ys' v) xs prf)
     new     : Handler e m =>
               res -> 
               EffM m a (MkEff res e :: xs) (\v => (MkEff res' e :: xs')) ->
               EffM m a xs (\v => xs')
     catch   : Catchable m err =>
               EffM m a xs xs' -> (err -> EffM m a xs xs') ->
               EffM m a xs xs'

     (:-)    : (l : ty) -> 
               EffM m t [x] xs' -> -- [x] (\v => xs) -> 
               EffM m t [l ::: x] (\v => map (l :::) (xs' v))

{-
syntax [tag] ":!" [val] = !(tag :- val)

--   Eff : List (EFFECT m) -> Type -> Type
-}

implicit
lift' : EffM m t ys ys' ->
        {default tactics { byReflection reflectEff; }
           prf : SubList ys xs} ->
        EffM m t xs (\v => updateWith (ys' v) xs prf)
lift' e {prf} = lift prf e

implicit
effect' : {a, b: _} -> {e : Effect} ->
          (eff : e t a b) ->
          {default tactics { byReflection reflectEff; }
             prf : EffElem e a xs} ->
         EffM m t xs (\v => updateResTy v xs prf eff)
effect' e {prf} = effect prf e

return : a -> EffM m a xs (\v => xs)
return x = value x

-- for idiom brackets

infixl 2 <$>

pure : a -> EffM m a xs (\v => xs)
pure = value

(<$>) : EffM m (a -> b) xs (\v => xs) -> 
        EffM m a xs (\v => xs) -> EffM m b xs (\v => xs)
(<$>) prog v = do fn <- prog
                  arg <- v
                  return (fn arg)

-- an interpreter

private
execEff : Env m xs -> (p : EffElem e res xs) ->
          (eff : e a res resk) ->
          ((v : a) -> Env m (updateResTy v xs p eff) -> m t) -> m t
execEff (val :: env) Here eff' k
    = handle val eff' (\v, res => k v (res :: env))
execEff (val :: env) (There p) eff k
    = execEff env p eff (\v, env' => k v (val :: env'))

-- Q: Instead of m b, implement as StateT (Env m xs') m b, so that state
-- updates can be propagated even through failing computations?

eff : Env m xs -> EffM m a xs xs' -> ((x : a) -> Env m (xs' x) -> m b) -> m b
eff env (value x) k = k x env
eff env (prog >>= c) k
   = eff env prog (\p', env' => eff env' (c p') k)
eff env (effect prf effP) k = execEff env prf effP k
eff env (lift prf effP) k
   = let env' = dropEnv env prf in
         eff env' effP (\p', envk => k p' (rebuildEnv envk prf env))
eff env (new r prog) k
   = let env' = r :: env in
         eff env' prog (\p' => \ (v :: envk) => k p' envk)
eff env (catch prog handler) k
   = catch (eff env prog k)
           (\e => eff env (handler e) k)
-- FIXME:
-- xs is needed explicitly because otherwise the pattern binding for
-- 'l' appears too late. Solution seems to be to reorder patterns at the
-- end so that everything is in scope when it needs to be.
eff {xs = [l ::: x]} env (l :- prog) k
   = let env' = unlabel env in
         eff env' prog (\p', envk => k p' (relabel l envk))

run : Applicative m => Env m xs -> EffM m a xs xs' -> m a
run env prog = eff env prog (\r, env => pure r)

runEnv : Applicative m => Env m xs -> EffM m a xs xs' -> 
         m (x : a ** Env m (xs' x))
runEnv env prog = eff env prog (\r, env => pure (r ** env))

runPure : Env id xs -> EffM id a xs xs' -> a
runPure env prog = eff env prog (\r, env => r)

-- runPureEnv : Env id xs -> EffM id a xs xs' -> (x : a ** Env id (xs' x))
-- runPureEnv env prog = eff env prog (\r, env => (r ** env))

runWith : (a -> m a) -> Env m xs -> EffM m a xs xs' -> m a
runWith inj env prog = eff env prog (\r, env => inj r)

Eff : (Type -> Type) -> Type -> List EFFECT -> Type
Eff m t xs = EffM m t xs (\v => xs)

-- some higher order things

mapE : Applicative m => (a -> Eff m b xs) -> List a -> Eff m (List b) xs
mapE f []        = pure []
mapE f (x :: xs) = [| f x :: mapE f xs |]

when : Applicative m => Bool -> Eff m () xs -> Eff m () xs
when True  e = e
when False e = pure ()

