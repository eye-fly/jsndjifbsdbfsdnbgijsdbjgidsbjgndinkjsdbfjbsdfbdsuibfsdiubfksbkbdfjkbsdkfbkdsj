module Runner where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import AbsGramar  
import Util

data Env = Env (Map Ident Int) (Map Ident TopDef) 
type Glob = (Map Ident Int, Map Int String, Int)

getS:: Ord a => Map a b -> a-> b 
getS mp k =  case Map.lookup k mp of
    (Just v)-> v

getVar::  Env -> Glob ->Ident -> Int
getVar (Env vars _) (globv,_,_) ident = case Map.lookup ident vars of
    (Just v) -> v
    Nothing -> getS globv ident

addVar:: Ident -> Int -> Env -> Env
addVar ident val (Env vars funvs) =
    (Env (Map.insert ident val vars) funvs)

addString:: String -> Glob -> (Int,Glob)
addString str (globV,strs, newNr) =
    (newNr, (globV,Map.insert newNr str strs, newNr+1))
getString:: Int -> Glob -> String
getString k (_, strs, _) = case Map.lookup k strs of
    (Just s) -> s

getFun::  Env ->Ident -> TopDef 
getFun (Env _ funvs) = getS funvs

addFun:: Ident -> TopDef -> Env -> Env
addFun ident val (Env vars funs) =
    (Env vars (Map.insert ident val funs))

mapA::  (a -> b -> (c, a)) -> a -> [b] -> ([c], a)
mapA f a (h:t) = let (h2,a2) = f a h in 
    let (t2,a3) = mapA f a2 t in ((h2:t2), a3)

bToInt:: Bool -> Int  
bToInt x = if x then 1 else 0

calkExpresion:: Type -> Expr -> Env -> Glob -> (Int,Glob)
calkExpresion (Str pos) exp env glob = case exp of
    (EString _ str) -> addString str glob
    (EAdd _ exp1 (Plus _) exp2) -> let (x,glob2) = calkExpresion (Str pos) exp1 env glob in let(x2,glob3) = calkExpresion (Str pos) exp2 env glob2 in
        addString (getString x glob ++ (getString x2 glob)) glob
calkExpresion tp exp env glob = case exp of
    (EVar _ ident) -> (getVar env glob ident,glob)
    (ELitInt _ x) -> (fromIntegral x,glob)
    (ELitTrue _) -> (1,glob)
    (ELitFalse _) -> (0,glob)
    (EApp _ ident exprs) -> let (arg,glob2) = mapA (\a_g exp2 -> calkExpresion tp exp2 env a_g) glob exprs in 
        calkFunc (getFun env ident) arg env glob2
    (Neg _ expr2) -> let (x,glob2) = calkExpresion tp expr2 env glob in (-x,glob2)
    (Not _ expr2) -> let (x,glob2) = calkExpresion tp expr2 env glob in (mod (x+1) 2,glob2)
    (EMul _ expr2 op expr3) -> let (x,glob2) = calkExpresion tp expr2 env glob in let(x2,glob3) = calkExpresion tp expr3 env glob2 in
        case op of 
            (Times _) -> (x*x2, glob3)
            (Div _) -> (x `quot` x2, glob3)
            (Mod _) -> (mod x x2, glob3)
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

fold2l f a [] []    = a
fold2l f a (x:xs) (y:ys) = let a' = f a x y
                    in fold2l f a' xs xy

calkStmts:: [Stmt] -> Type -> Env -> Glob -> (Int,Glob)
calkStmts [] _ _ glob = (0,glob)
calkStmts (stmt:stmts) retType env glob = case stmt of
    (Empty _) -> calkStmts calkStmts env glob
    (Decl _ tp (Init _ Ident exp) ) -> let (val,glob') =calkExpresion tp expr env glob in
        calkStmts calkStmts (addVar Ident val env) glob
    (Ass _ Ident exp ) -> let (val,glob') =calkExpresion tp <<<<<<<<<<<<< expr env glob in
        calkStmts calkStmts (addVar Ident val env) glob

calkFunc:: TopDef -> [Int] -> Env -> Glob -> (Int,Glob)
calkFunc (_ tp _ argIn (Block _ stmts)) argV env glob = (0,glob)
    let env' = fold2l (\a (Arg _ _ ident) val -> addVar ident val a) env argIn argV in
        foldl (\a )

(foldl (\a x->Map.insert (hasIdent x) x a) Map.empty funcs)

preRun:: [AbsGramar.TopDef] -> Env -> Env
preRun p env = env
    -- case p of
    --     h:t-> case h of 
    --         (FnDef _ _ _ _ _) -> preRun t globVars (h:funcs)
    --         _ -> preRun t (h:globVars) funcs
    --     [] -> do
    --         let err = checkForDuplicates globVars Set.empty in if err == Nothing then
    --             (checkForDuplicates funcs Set.empty, globVars, funcs)
    --         else 
    --             (err, globVars, funcs)

runer:: [AbsGramar.TopDef] -> Int
runer p = 
    let env = preRun p (Env Map.empty Map.empty) in 
    0