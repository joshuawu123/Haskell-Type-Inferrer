{-
  You will be filling in the gaps to implement simple type inference.  Please
  provide an implementation for all functions that raise the "ToImplement"
  exception.

  Feel free to add additional functions as you wish.
 -}
module TypeInfer (inferType) where
import Control.Exception
import Data
import Utils
import Debug.Trace as Trace
import Data.List as List

unify :: (Type, Type) -> Subst
unify (t1, t2@(TVar tvar)) = if not (occursIn t1 t2) then [(tvar, t1)] else throw TypeCircularity
unify (t1@(TVar tvar), t2) = if not (occursIn t2 t1) then [(tvar, t2)] else throw TypeCircularity 
unify (TBase t1, TBase t2) = --[]
      if t1 == t2 then idSubst else throw (TypeMismatch (TBase t1) (TBase t2))
unify (TArrow t11 t12, TArrow t21 t22) =
      let s1 = unify (t11,t21)
          s2 = unify (applySubst t12 s1, applySubst t22 s1)
      --in s2 ++ s1
      in s1 ++ s2
unify t@_ = if null t then [] else Trace.trace ("\nErr: " ++ show t) throw (Default "Fail")

unifySet :: Constraints -> Subst
unifySet constrList = 
  if null constrList then [] 
  else let s = unify (head constrList)
       in if null s then --Trace.trace ("s: " ++ show (fst (head s)) ++ "," ++ show (snd (head s)) ++ "\n") 
         s ++ unifySet (tail constrList) 
         else --Trace.trace ("s: " ++ show (fst (head s)) ++ "," ++ show (snd (head s)) ++ "\n")  
           (s ++ (unifySet (substAll (TVar (fst (head s))) (snd (head s)) (tail constrList))))

--only used for circular type error
containsType :: [(String, Type)] -> Ident -> Bool
containsType tenv id = if null tenv then False else if (id == fst (head tenv)) then True else containsType (tail tenv) id

addTypeEnv :: ConstraintEnv -> Ident -> Type -> ConstraintEnv
addTypeEnv cenv newVar varType = if (containsType (tenv cenv) newVar) then  throw TypeCircularity else
  CEnv {constraints = constraints cenv, var = var cenv, tenv = (newVar, varType) : tenv cenv}


findVarType :: Ident -> TEnv -> Type
findVarType varID (varmap : rest) = 
  if varID == fst varmap then snd varmap else findVarType varID rest
findVarType varID [] = throw (UnboundVar varID)

--gets max of two var values
getNextNum :: ConstraintEnv -> ConstraintEnv -> Int 
getNextNum c1 c2 = max (var c1) (var c2)

--set the var value in a cenv
setVal :: ConstraintEnv -> Int -> ConstraintEnv 
setVal cenv v =
  CEnv {constraints = constraints cenv, var = v, tenv = tenv cenv}

--clear the cenv of constraints, used in returning primitives/tvars
removeConstraints :: ConstraintEnv -> ConstraintEnv
removeConstraints cenv = 
  CEnv {constraints = [], var = var cenv, tenv = tenv cenv}

--puts it into a list form. e.g. [("x", TVar "x")]
parseLetStmt :: Stmt -> [(Ident, Exp)]
parseLetStmt s = case s of 
  SEmpty -> []
  SAssign id exp -> [(id,exp)]
  SSeq s1 s2 -> parseLetStmt s1 ++ parseLetStmt s2

--add bindings from let statement
--ex. let x = E1, y = E2, z = E3 in E, adds x:tx, y:ty, z:tz
addNewBindings :: ConstraintEnv -> [(Ident, Exp)] -> ConstraintEnv
addNewBindings cenv parsedLet = if null parsedLet then cenv else
  addNewBindings (addTypeEnv cenv (fst (head parsedLet)) (TVar (fst (head parsedLet)))) (tail parsedLet) --this might be wrong, should probably be using newTVar?

--add bindings from let statement
--ex. let x = E1, y = E2, z = E3 in E, adds x:tx, y:ty, z:tz
--returns the cenv and a list of the new bindings to add
letEvaluate :: ConstraintEnv -> [(Ident, Exp)] -> TEnv -> (ConstraintEnv, TEnv)
letEvaluate cenv parsedLet tenv = if null parsedLet then (cenv,tenv) else 
    let retVal = inferTypes cenv (snd (head parsedLet))
        newEnv = (fst retVal)
        newType = (snd retVal)
        substitutions = unifySet (constraints newEnv)  --calculate substitutions
        finalType = applySubst newType substitutions --get the new type and create a binding
        tmpTenv = tenv ++ [((fst (head parsedLet)), finalType)] --add the new bindings to a return list
    in letEvaluate cenv (tail parsedLet) tmpTenv

--add all bindings from a tenv list
addAllBindings :: ConstraintEnv -> TEnv -> ConstraintEnv
addAllBindings cenv tenvList = if null tenvList then cenv else addAllBindings (addTypeEnv cenv (fst (head tenvList)) (snd (head tenvList))) (tail tenvList)

{- Performs type inference. -}
--ConstraintEnv = (constraints,var,tenv) = ([(Type, Type)],Int,[(String, Type)])
inferTypes :: ConstraintEnv -> Exp -> (ConstraintEnv, Type)
inferTypes cenv (EVar var) = (removeConstraints cenv, findVarType var (tenv cenv))
inferTypes cenv (ELambda v body) =
  let new = newTVar cenv --use given function newTVar which gets the t# and increments the cenv var 
      boundType = fst new --this is the type of this lambda
      updatedEnv = addTypeEnv (snd new) v boundType --add to the typeEnv
      ret = (inferTypes updatedEnv body) --call infertypes on the body
  in ((fst ret), TArrow boundType (snd ret)) --new type is this type -> return of right side type
inferTypes cenv (EApp fn arg) =  --return the t type of the arguments in tenv, type the application term, once both are done increment the int and create a new tvar, create new constraint left = right->up
  let retLeft = inferTypes cenv fn --return of left side
      tmpEnv = setVal cenv (var (fst retLeft)) --get the var of the leftside so the rightside uses that var
      retRight = inferTypes tmpEnv arg --return of right side
      tmp = setVal cenv (getNextNum (fst retLeft) (fst retRight)) --gets the max of the two return vars to know which one to use
      new = newTVar tmp 
      boundType = fst new
      newEnv0 = addConstraints (snd new) (constraints (fst retLeft)) --add constraints from left side
      newEnv1 = addConstraints newEnv0 (constraints (fst retRight)) --add constraints from right side
      newEnv2 = addConstraint newEnv1 (snd retLeft) (TArrow (snd retRight) boundType) --add new constraint, left type = right type -> this type
  in (newEnv2, boundType)
inferTypes cenv (ECond pred tbody fbody) = 
  let retPred = inferTypes cenv pred
      tmpEnv = setVal cenv (var (fst retPred)) --update var changed from pred
      newEnv1 = addConstraint tmpEnv (snd retPred) boolType --constraint for Tpred = bool
      retTBody = inferTypes newEnv1 tbody
      newEnv2 = setVal newEnv1 (var (fst retTBody)) --update var changed from tbody
      retFBody = inferTypes newEnv2 fbody
      newEnv3 = addConstraint newEnv2 (snd retTBody) (snd retFBody) --constraint for Ttbody = Tfbody
      newEnv4 = addConstraints newEnv3 (constraints (fst retTBody)) --constraints from tbody
      newEnv5 = addConstraints newEnv4 (constraints (fst retFBody)) --constraints from fbody
      newEnv6 = addConstraints newEnv5 (constraints (fst retPred)) --constraints from pred
      new = newTVar newEnv6
      boundType = fst new
      newEnv7 = snd new
  in (newEnv7, snd retTBody)
inferTypes cenv (EPlus op1 op2) = 
  let retLeft = inferTypes cenv op1 --return of left side
      tmpEnv = setVal cenv (var (fst retLeft))
      retRight = inferTypes tmpEnv op2 --return of right side 
      tmp = setVal cenv (getNextNum (fst retLeft) (fst retRight)) --gets the max of the two return vars to know which one to use, not entirely sure if correct
      new = newTVar tmp
      boundType = fst new
      newEnv1 = addConstraints (snd new) (constraints (fst retLeft)) --add constraints from left side
      newEnv2 = addConstraints newEnv1 (constraints (fst retRight)) --add constraints from right side
      newEnv3 = addConstraint newEnv2 (snd retLeft) intType --add constraint left type = int
      newEnv4 = addConstraint newEnv3 (snd retRight) intType --add constraint right type = int
      newEnv5 = addConstraint newEnv4 boundType intType --add constraint this type = int
  in (newEnv5, boundType)
inferTypes cenv (EPrim (PNum _)) = (removeConstraints cenv, intType)
inferTypes cenv (EPrim (PBool _)) = (removeConstraints cenv, boolType)
inferTypes cenv (ELet s body) =
  let parsedLet = parseLetStmt s --first call parseLetStmt, then add all the new bindings
      newEnv0 = addNewBindings cenv parsedLet
      evalRet = letEvaluate newEnv0 parsedLet [] --then evaluate each of the expressions from parse, and add all constraints
      newEnv1 = addAllBindings cenv (snd evalRet) --add the newly created bindings 
      ret = inferTypes newEnv1 body
    in ret --Trace.trace ("eval: " ++ (fst (head (snd evalRet))) ++ ": " ++ show (snd (head (snd evalRet))))   ret --not 100% sure about this 


{- Top-level type inference function. I will be calling it on Submitty. -}
inferType :: Exp -> Type
inferType exp = 
  let initialEnv = CEnv [] 0 [] 
      (solvedEnv, finalType) = inferTypes initialEnv exp
      substitutions = unifySet (constraints solvedEnv)
  in applySubst finalType substitutions
  --in Trace.trace ("type: " ++ show finalType ++ "\nenv: " ++ (cStr (constraints solvedEnv))) applySubst finalType substitutions -- ++ "\nsubs: " ++ show substitutions


---for debugging
cStr :: Constraints -> String
cStr c = if null c then "" else (show (fst (head c))) ++ "," ++ (show (snd (head c)))  ++ "            " ++ cStr (tail c)