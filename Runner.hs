module Runner where

import System.IO  
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import AbsGramar  
import Util

data Env = Env (Map Ident (Int,Type)) (Map Ident TopDef) 

data Status = Sok | Serr | Sbreak | Scontinue


type Glob = (Map Ident (Int,Type), Map Int String, Int, IO(), Status)

newEnv:: Env -> Env
newEnv (Env _ funcs) = Env Map.empty funcs

getS:: Ord a => Map a b -> a-> b 
getS mp k =  case Map.lookup k mp of
    (Just v)-> v

getVar::  Env -> Glob ->Ident -> Int
getVar (Env vars _) (globv,_,_,_,_) ident = case Map.lookup ident vars of
    (Just (v,_)) -> v
    Nothing ->fst $ getS globv ident
getVarT::  Env -> Glob ->Ident -> Type
getVarT (Env vars _) (globv,_,_,_,_) ident = case Map.lookup ident vars of
    (Just (_,t)) -> t
    Nothing -> snd $ getS globv ident

addVar:: Ident -> (Int,Type) -> Env -> Env
addVar ident val (Env vars funvs) =
    (Env (Map.insert ident val vars) funvs)

isVarLocal:: Env ->Ident -> Bool
isVarLocal (Env vars _) ident = case Map.lookup ident vars of
    (Just (_,t)) -> True
    Nothing -> False


addGlob:: Ident -> (Int,Type) -> Glob -> Glob
addGlob ident val (vars, strs, srt_nr, io, status) =
    ((Map.insert ident val vars), strs, srt_nr, io, status)

addString:: String -> Glob -> (Int,Glob)
addString str (globV,strs, newNr, io, status) =
    (newNr, (globV,Map.insert newNr str strs, newNr+1, io, status))
getString:: Int -> Glob -> String
getString k (_, strs, _,_,_) = case Map.lookup k strs of
    (Just s) -> s

getFun::  Env ->Ident -> TopDef 
getFun (Env _ funvs) = getS funvs

addFun:: Ident -> TopDef -> Env -> Env
addFun ident val (Env vars funs) =
    (Env vars (Map.insert ident val funs))

-- mapA::  (a -> b -> t -> (c, a)) -> a -> [b] -> [t]-> ([c], a)
mapA _ a [] [] = ([],a)
mapA f a (h:t) ((Arg _ th _):ts) = let (h2,a2) = f a h th in 
    let (t2,a3) = mapA f a2 t ts in ((h2:t2), a3)

bToInt:: Bool -> Int  
bToInt x = if x then 1 else 0

printLine:: String  -> Handle -> Glob -> Glob
printLine str handle (globV,strs, newNr, io, status) =
    (globV,strs, newNr, io >> (hPutStrLn handle str), status )

getStatus:: Glob -> Status
getStatus (_, _, _,_,status)= status

setStatus:: Status -> Glob -> Glob
setStatus st (globV,strs, newNr, io, _)=  (globV,strs, newNr, io, st)

calkExpresion:: Type -> Expr -> Env -> Glob -> (Int,Glob)
calkExpresion tp (EVar _ ident) env glob = (getVar env glob ident,glob)
calkExpresion (Str pos) exp env glob = case exp of
    -- (EVar _ ident) -> (getVar env glob ident,glob)
    (EString _ str) -> addString str glob
    (EAdd _ exp1 (Plus _) exp2) -> let (x,glob2) = calkExpresion (Str pos) exp1 env glob in let(x2,glob3) = calkExpresion (Str pos) exp2 env glob2 in
        addString (getString x glob3 ++ (getString x2 glob3)) glob3
calkExpresion tp exp env glob = case exp of
    -- (EVar _ ident) -> (getVar env glob ident,glob)
    (ELitInt _ x) -> (fromInteger x,glob)
    (ELitTrue _) -> (1,glob)
    (ELitFalse _) -> (0,glob)
    (EApp _ ident exprs) -> let fun  = getFun env ident in let (FnDef _ _ _ aTps _) = fun in
        let (arg,glob2) = mapA (\a_g exp2 aTp -> calkExpresion aTp exp2 env a_g) glob exprs aTps in 
        calkFunc ident fun arg (newEnv env) glob2
    (Neg _ expr2) -> let (x,glob2) = calkExpresion tp expr2 env glob in (-x,glob2)
    (Not _ expr2) -> let (x,glob2) = calkExpresion tp expr2 env glob in (mod (x+1) 2,glob2)
    (EMul _ expr2 op expr3) -> let (x,glob2) = calkExpresion tp expr2 env glob in let(x2,glob3) = calkExpresion tp expr3 env glob2 in
        case op of 
            (Times _) -> (x*x2, glob3)
            (Mod _) -> (mod x x2, glob3)
            (Div pos) -> if x2 == 0 then (0, printLine ("try to div by 0 at "++showPosition pos ) stderr (setStatus Serr glob3))  else (x `quot` x2, glob3)
    (EAdd _ expr2 op expr3) -> let (x,glob2) = calkExpresion tp expr2 env glob in let(x2,glob3) = calkExpresion tp expr3 env glob2 in
        case op of 
            (Plus _) -> (x+x2, glob3)
            (Minus _) -> (x-x2, glob3)
    (ERel _ expr2 op expr3) -> let (x,glob2) = calkExpresion tp expr2 env glob in let(x2,glob3) = calkExpresion tp expr3 env glob2 in
        case op of 
            (LTH _) -> (bToInt $ x < x2, glob3)
            (LE _) -> (bToInt $ x <= x2, glob3)
            (GTH _) -> (bToInt $ x > x2, glob3)
            (GE _) -> (bToInt $ x >= x2, glob3)
            (EQU _) -> (bToInt $ x == x2, glob3)
            (NE _) -> (bToInt $ x /= x2, glob3)
    (EAnd _ expr2 expr3) -> let (x,glob2) = calkExpresion tp expr2 env glob in let(x2,glob3) = calkExpresion tp expr3 env glob2 in
            (bToInt $ x+x2 == 2, glob3)
    (EOr _ expr2 expr3) -> let (x,glob2) = calkExpresion tp expr2 env glob in let(x2,glob3) = calkExpresion tp expr3 env glob2 in
            (bToInt $ x+x2 >= 1, glob3)

    -- (Int _) -> case exp of
emtyCode :: [Stmt]
emtyCode = [Empty BNFC'NoPosition]

whileLoop::  [Stmt] -> [Stmt] -> Expr -> Type -> Env -> Glob -> (Maybe Int, Env, Glob)
whileLoop _ _ _ _ env (globV,strs, newNr, io, Serr) = (Nothing, env, (globV,strs, newNr, io, Serr))
whileLoop st stRest exp retType env glob = 
    let (val,glob') = calkExpresion (Bool BNFC'NoPosition) exp env glob in
        if val == 1 then case  calkStmts st retType env glob' of
            (Nothing, env', glob'') -> whileLoop st stRest exp retType env' glob''
            out -> out
        else calkStmts stRest retType env glob'

loop:: [Stmt] -> [Stmt] -> Ident -> Expr -> Type -> Env -> Glob -> (Maybe Int, Env, Glob)
loop _ _ _ _ _ env (globV,strs, newNr, io, Serr) = (Nothing, env, (globV,strs, newNr, io, Serr))
loop st stRest ident exp retType env glob = 
    let (targetVal,glob') = calkExpresion (Int BNFC'NoPosition) exp env glob in
    let varVal = getVar env glob' ident in
        if targetVal >= varVal then case  calkStmts st retType env glob' of
            (Nothing, env', glob'') -> loop st stRest ident exp retType (addVar ident (varVal+1, getVarT env' glob'' ident) env') glob''
            out -> out
        else calkStmts stRest retType env glob'

runWCondition:: [Stmt] -> [Stmt] ->[Stmt] -> Expr -> Type -> Env -> Glob -> (Maybe Int, Env, Glob)
runWCondition st1 st2 stRest exp retType env glob = 
    let (val,glob') = calkExpresion (Bool BNFC'NoPosition) exp env glob in
        case (if val == 1 then calkStmts st1 else calkStmts st2 ) retType env glob' of
            (Nothing, _, glob'') -> calkStmts stRest  retType env glob''
            out -> out

calkStmts:: [Stmt] -> Type -> Env -> Glob -> (Maybe Int, Env,Glob)
calkStmts _ _ env (globV,strs, newNr, io, Serr) = (Nothing, env, (globV,strs, newNr, io, Serr))
calkStmts [] _ env glob = (Nothing,env,glob)
calkStmts (stmt:stmts) retType env glob = case stmt of
    (Empty _) -> calkStmts stmts retType env glob
    (Decl _ tp (Init _ ident exp) ) -> let (val,glob') =calkExpresion tp exp env glob in
        calkStmts stmts retType (addVar ident (val,tp) env) glob'
    (Ass _ ident exp ) -> let tp =  getVarT env glob ident in let (val,glob') =calkExpresion tp exp env glob in
        if isVarLocal env ident then
            calkStmts stmts retType (addVar ident (val,tp) env) glob' else
            calkStmts stmts retType env (addGlob ident (val,tp) glob')
    (Ret _ exp) -> let (rt,glob')= calkExpresion retType exp env glob in (Just rt, env, glob')
    (Cond pos exp (Block _ stmts1)) -> runWCondition stmts1 emtyCode stmts exp retType env glob
    (CondElse _ exp (Block _ stmts1) (Block _ stmts2) ) -> runWCondition stmts1 stmts2 stmts exp retType env glob
    (While _ exp (Block _ stmts1) ) -> whileLoop stmts1 stmts exp retType env glob
    (For _ ident expS expE (Block _ stmts1) ) -> let (stVal,glob') = calkExpresion (Int BNFC'NoPosition) expS env glob in
         loop stmts1 stmts ident expE retType (addVar ident (stVal, (Int BNFC'NoPosition)) env) glob'
    -- to do for loop <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
calkStmtsDirect:: [Stmt] -> Type -> Env -> Glob -> (Int,Glob)
calkStmtsDirect stmts retType env glob = case calkStmts stmts retType env glob of
    (Nothing, _, glob') -> (0, glob')
    (Just rt, _, glob') -> (rt,glob')


fold2l f a [] []    = a
fold2l f a (x:xs) (y:ys) = let a' = f a x y in
     fold2l f a' xs ys
calkFunc:: Ident -> TopDef -> [Int] -> Env -> Glob -> (Int,Glob)
calkFunc (Ident "printInt") _ [val] env glob = (0,printLine (show val) stdout glob)
calkFunc (Ident "printInt") _ _ env glob = (-1,printLine ("printInt err") stdout glob)
calkFunc (Ident "printString") _ [val] env glob = (0,printLine (getString val glob) stdout glob)
calkFunc (Ident "printString") _ _ env glob = (-1,printLine ("printInt err") stdout glob)

calkFunc _ (FnDef _ retTp _ argIn (Block _ stmts)) argV env glob = 
    let env' = fold2l (\a (Arg _ tp ident) val -> addVar ident (val,tp) a) env argIn argV in
        calkStmtsDirect stmts retTp env' glob
    -- (0,glob)

-- (foldl (\a x->Map.insert (hasIdent x) x a) Map.empty funcs)

emptyFun:: Ident -> Type -> Env -> Env
emptyFun ident tp = addFun ident (FnDef BNFC'NoPosition (Int BNFC'NoPosition) ident [(Arg BNFC'NoPosition tp (Ident "input"))] (Block BNFC'NoPosition []))

preRun:: [AbsGramar.TopDef] -> (Env, Glob) -> (Env,Glob)
preRun p (env,glob) = 
    case p of
        h:t-> case h of 
            (FnDef _  _ ident _ _) -> preRun t (addFun ident h env ,glob)
            (GlobDecl _ tp (Init _ ident exp))-> let (val,glob') = calkExpresion tp exp env glob in preRun t (env ,addGlob ident (val,tp) glob)
        [] -> ( emptyFun (Ident "printString") (Str BNFC'NoPosition) $ emptyFun (Ident "printInt") (Int BNFC'NoPosition) env,glob)

runer:: [AbsGramar.TopDef] -> (Int,IO ())
runer p = 
    let (env,glob) = preRun p ((Env Map.empty Map.empty),( Map.empty,  Map.empty, 0, pure (),Sok) ) in 
        let (ret, (_,_,_, io,status)) = calkFunc  (Ident "main") (getFun env (Ident "main")) [] env glob in
        -- let (ret, (_,_,_, io)) = calkFunc  (Ident "printInt") (getFun env (Ident "main")) [10] env glob in
            case status of
                Serr -> (-1,io)
                _ -> (ret,io )