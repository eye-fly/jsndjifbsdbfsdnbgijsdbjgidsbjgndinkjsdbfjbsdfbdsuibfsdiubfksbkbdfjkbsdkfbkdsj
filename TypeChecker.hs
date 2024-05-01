module TypeChecker where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import AbsGramar  
import Util

type Type = String

checkForDuplicates:: [AbsGramar.TopDef] -> Set String -> Err
checkForDuplicates lst st = 
    case lst of 
        h:t -> let s = Util.hasIdent h in if Set.member s st then
            Just ("Identyfiers must be uniqe " ++ (showPosition $ AbsGramar.hasPosition h))
        else
            checkForDuplicates t (Set.insert s st)

        _ -> Nothing

typeChecker:: [AbsGramar.TopDef] -> [AbsGramar.TopDef] -> [AbsGramar.TopDef]-> Err
typeChecker p globVars funcs = 
    case p of
        h:t-> case h of 
            (FnDef _ _ _ _ _) -> typeChecker t (h:globVars) funcs
            _ -> typeChecker t globVars (h:funcs)
        [] -> do
            let err = checkForDuplicates globVars Set.empty in if err == Nothing then
                checkForDuplicates funcs Set.empty
            else 
                err
-- global local
data Vars = Vars (Map String AbsGramar.TopDef) (Map String AbsGramar.Stmt ) 

addLocalVar:: AbsGramar.Ident -> AbsGramar.Type -> Vars -> Vars
addLocalVar ident tp (Vars globVars localVars) = 
     Vars globVars (Map.insert (identToString ident) tp localVars)

addGlobalVar:: AbsGramar.Ident -> AbsGramar.Type -> Vars -> Vars
addGlobalVar ident tp (Vars globVars localVars) = 
     Vars (Map.insert (identToString ident) tp globVars) localVars

type Func = AbsGramar.TopDef
type Funcs = Map String Func

getGVarType:: Maybe AbsGramar.TopDef -> Maybe AbsGramar.Type
getGVarType (Just (GlobDecl _ typ _)) = Just typ
getGVarType _ = Nothing

getLVarType:: Maybe AbsGramar.Stmt -> Maybe AbsGramar.Type
getLVarType (Just (Decl _ typ _)) = Just typ
getLVarType _ = Nothing

getVar:: AbsGramar.Ident -> Vars -> Maybe AbsGramar.Type
getVar identT (Vars globVars localVars) =
    let ident = identToString identT in let local = getLVarType $ Map.lookup ident localVars in
    if local == Nothing then
        getGVarType $ Map.lookup ident globVars
    else
        local
        

getFuncType:: AbsGramar.Ident -> Funcs -> Maybe AbsGramar.Type
getFuncType ident funcs =
    let func = Map.lookup (identToString ident) funcs in
        case func of
            Just (FnDef _ tpe _ _ _) -> Just tpe
            _ -> Nothing

checkFuncArgsA:: [(Err, Maybe AbsGramar.Type)] -> [AbsGramar.Arg] -> AbsGramar.BNFC'Position -> Err
checkFuncArgsA givenA expectedA pos =  case (givenA,expectedA) of
    ([],[]) -> Nothing
    ([],_) -> Just ("delcared function has more arguments than was given at "++(showPosition pos))
    (_,[]) -> Just ("delcared function has less arguments than was given at "++(showPosition pos))
    (((Nothing,Just gHt):gT), ((Arg _ eHt _):eT)) -> if gHt/=eHt then
        Just ("mismach in arguments while calling a function at "++(showPosition pos)) else
        checkFuncArgsA gT eT pos
    (((gHe, _):gT), ((Arg _ eHt _):eT)) -> gHe



checkFuncArgs:: AbsGramar.Ident -> [(Err, Maybe AbsGramar.Type)] -> Funcs -> AbsGramar.BNFC'Position -> Err
checkFuncArgs identT givenArgs funcs pos =
    let ident = identToString identT in 
    let func = Map.lookup ident funcs in
        case func of
            Nothing -> Just ("use of undefined function at " ++(showPosition pos))
            Just (FnDef fDefPos _ _ args _) -> checkFuncArgsA givenArgs args pos



checkExpresion:: AbsGramar.Expr -> Funcs -> Vars -> (Err, Maybe AbsGramar.Type)
checkExpresion expr declFunc vars = 
    case expr of
        EVar pos ident -> let var = getVar ident vars in 
            if var == Nothing then (Just ("use of undefined variable "++(showPosition pos)), Nothing)
            else (Nothing, var)
        ELitInt pos _ -> (Nothing, Just (Int pos))
        ELitTrue pos -> (Nothing, Just (Bool pos))
        ELitFalse pos -> (Nothing, Just (Bool pos))
        EApp pos fIdent args -> let err = checkFuncArgs fIdent (map (\x -> checkExpresion x declFunc vars) args) declFunc pos in
            if err /= Nothing then (err, Nothing) else
                (Nothing, getFuncType fIdent declFunc)

checkFunction:: [AbsGramar.Stmt] -> Funcs -> Vars -> Err
checkFunction (funcH:funcT) declFunc vars = 
    case funcH of 
        Empty _ -> checkFunction funcT vars
        Decl pos dType (Init _ ident expr) -> let (err,eType) = checkExpresion expr declFunc vars in if err /= Nothing then err else
            if dType /= eType then Just ("wrong declared variable type at "++ (showPosition pos)) else
                checkFunction funcT (addLocalVar ident dType vars)

checkFunction [] declFunc vars = Nothing