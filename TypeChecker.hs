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

-- global local
type Vars = Map String (AbsGramar.Type, Bool)

-- addLocalVar:: AbsGramar.Ident -> AbsGramar.Type -> Vars -> Vars
-- addLocalVar ident tp (Vars globVars localVars) = 
--      Vars globVars (Map.insert (identToString ident) tp localVars)

addVar:: AbsGramar.Ident -> (AbsGramar.Type,Bool) -> Vars -> Vars
addVar ident tp vars = 
    Map.insert (identToString ident) tp vars

getVar:: AbsGramar.Ident -> Vars -> Maybe AbsGramar.Type
getVar ident vars = case Map.lookup (identToString ident) vars  of
    Nothing -> Nothing
    (Just (tp,_)) -> Just tp

isConst:: AbsGramar.Ident -> Vars -> Bool 
isConst ident vars = case Map.lookup (identToString ident) vars  of
    (Just (_,con)) -> con

type Func = AbsGramar.TopDef
type Funcs = Map String Func

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
    (((Nothing,Just gHt):gT), ((Arg _ eHt _):eT)) -> if gHt </> eHt then
        Just ("mismatch in arguments while calling a function at "++(showPosition pos)) else
        checkFuncArgsA gT eT pos
    (((gHe, _):gT), ((Arg _ eHt _):eT)) -> gHe



checkFuncArgs:: AbsGramar.Ident -> [(Err, Maybe AbsGramar.Type)] -> Funcs -> AbsGramar.BNFC'Position -> Err
checkFuncArgs identT givenArgs funcs pos =
    let ident = identToString identT in 
    let func = Map.lookup ident funcs in
        case func of
            Nothing -> Just ("use of undefined function at " ++(showPosition pos))
            Just (FnDef fDefPos _ _ args _) -> checkFuncArgsA givenArgs args pos



check_two_exp:: AbsGramar.Expr -> AbsGramar.Expr -> Funcs -> Vars -> AbsGramar.BNFC'Position -> (Err, Maybe AbsGramar.Type)
check_two_exp expr1 expr2 declFunc vars pos = case checkExpresion expr1 declFunc vars of
    (Nothing, Just ex1T) -> case checkExpresion expr2 declFunc vars of
        (Nothing, Just ex2T) -> if ex1T <=> ex2T then (Nothing, Just ex1T) else (Just("mismatch of types it "++ (showPosition pos)++"\n got types "++ (show ex1T)++" and "++(show ex2T)),Nothing)
        (err, _) -> (err, Nothing)
    (err, _) -> (err, Nothing)
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
        EString pos _ -> (Nothing, Just (Str pos))
        Neg pos expr2 -> case checkExpresion expr2 declFunc vars of
            (Nothing, Just tp) -> if tp </> (Int pos) then (Just ("cannot nagate type that isn't a Int "++(showPosition pos) ),Nothing) else
                (Nothing, Just tp)
            (err, _) -> (err,Nothing)
        Not pos expr2 -> case checkExpresion expr2 declFunc vars of
            (Nothing, Just tp) -> if tp </> (Bool pos) then (Just ("cannot 'NOT' type that isn't a Bool "++(showPosition pos) ),Nothing) else
                (Nothing, Just tp)
            (err, _) -> (err,Nothing)
        EMul pos ex1 _ ex2 -> case check_two_exp ex1 ex2 declFunc vars pos of
            (Nothing, Just (Int pos)) -> (Nothing, Just (Int pos))
            (Nothing, _) -> (Just ("only int can be multiplied "++(showPosition pos) ),Nothing)
            (err,_)-> (err,Nothing)
        EAdd pos ex1 _ ex2 -> case check_two_exp ex1 ex2 declFunc vars pos of
            (Nothing, Just (Bool pos)) -> (Just ("bool can not be added "++(showPosition pos) ),Nothing)
            (Nothing, Just tp) -> (Nothing, Just tp)
            (err,_)-> (err,Nothing)
        ERel pos ex1 _ ex2 -> case check_two_exp ex1 ex2 declFunc vars pos of
            (Nothing, _)-> (Nothing, Just (Bool BNFC'NoPosition))
            (err,_)-> (err,Nothing)
        EAnd pos ex1 ex2 -> case check_two_exp ex1 ex2 declFunc vars pos of
            (Nothing, Just (Bool pos)) -> (Nothing, Just (Bool pos))
            (Nothing, _) -> (Just ("only boold can be '&&' "++(showPosition pos) ),Nothing)
            (err,_)-> (err,Nothing)
        EOr pos ex1 ex2 -> case check_two_exp ex1 ex2 declFunc vars pos of
            (Nothing, Just (Bool pos)) -> (Nothing, Just (Bool pos))
            (Nothing, _) -> (Just ("only boold can be '||' "++(showPosition pos) ),Nothing)
            (err,_)-> (err,Nothing)


checkFunction:: [AbsGramar.Stmt] -> AbsGramar.Type -> Funcs -> Vars -> Err
checkFunction [] _ _ check_two_exp = Nothing
checkFunction (funcH:funcT) retTyp declFunc vars = 
    case funcH of 
        Empty _ -> checkFunction funcT retTyp declFunc vars
        Decl pos dType (Init _ ident expr) -> case checkExpresion expr declFunc vars of
            (Nothing,Just eType) -> if dType </> eType then Just ("wrong declared variable type at "++ (showPosition pos)++"\n expected "++(show dType)++" but got "++ (show eType)) else
                checkFunction funcT retTyp declFunc (addVar ident (dType,False) vars)
            (err, _) -> err
        Ass pos ident expr -> case getVar ident vars of
            (Nothing) -> Just ("assigment to undaclared variable "++ (showPosition pos))
            Just tp1 -> case checkExpresion expr declFunc vars of
                (Nothing, Just tp2) -> if tp1 </> tp2 then Just ("mismatch of a type during assigment at "++ (showPosition pos)++"\n expected "++(show tp1)++" but got "++ (show tp2)) else
                     if isConst ident vars then Just ("assigment to constant variable at "++ (showPosition pos)) else
                    checkFunction funcT retTyp declFunc vars
                (err, _) -> err
        Ret pos expr -> case checkExpresion expr declFunc vars of
            (Nothing, Just tp) -> if tp </> retTyp then Just ("mismatch of a returened type at "++ (showPosition pos)++"\n expected "++(show retTyp)++" but got "++ (show tp)) else
                checkFunction funcT retTyp declFunc vars
            (err, _) -> err
        Cond pos bExpr (Block _ ifStmts) -> case checkExpresion bExpr declFunc vars of
            (Nothing, Just (Bool _)) -> case checkFunction ifStmts retTyp declFunc vars of
                Nothing -> checkFunction funcT retTyp declFunc vars
                err -> err
            (Nothing, Just tp) -> Just ("in if statment expresion is expected to have bool type at "++(showPosition pos)++ "\n but got "++(show tp) )
            (err, _) -> err
        CondElse pos bExpr (Block _ thenStmts) (Block _ elseStmts) -> case checkExpresion bExpr declFunc vars of
            (Nothing, Just (Bool _)) -> case (checkFunction thenStmts retTyp declFunc vars, checkFunction elseStmts retTyp declFunc vars) of
                (Nothing,Nothing) -> checkFunction funcT retTyp declFunc vars
                (Nothing, err) -> err
                (err,_) -> err
            (Nothing, Just tp) -> Just ("in if statment expresion is expected to have bool type at "++(showPosition pos)++ "\n but got "++(show tp) )
            (err, _) -> err
        While pos bExpr (Block _ whileStmts) -> case checkExpresion bExpr declFunc vars of
            (Nothing, Just (Bool _)) -> case checkFunction whileStmts retTyp declFunc vars of
                Nothing -> checkFunction funcT retTyp declFunc vars
                err -> err
            (Nothing, Just tp) -> Just ("in while expresion is expected to have bool type at "++(showPosition pos)++ "\n but got "++(show tp) )
            (err, _) -> err
        For pos ident b1Expr b2Expr (Block _ forStmts) -> case (checkExpresion b1Expr declFunc vars,checkExpresion b2Expr declFunc vars) of
            ((Nothing, Just (Int _)), (Nothing, Just (Int _))) -> case checkFunction forStmts retTyp declFunc (addVar ident ((Int pos),True) vars) of
                Nothing -> checkFunction funcT retTyp declFunc vars
                err -> err
            ((Nothing, Just (Int _)), (Nothing, Just tp)) -> Just ("in for expresion is expected to have int type at "++(showPosition $ hasPosition tp)++ "\n but got "++(show tp) )
            ((Nothing, Just tp),      (Nothing, Just (Int _))) -> Just ("in for expresion is expected to have int type at "++(showPosition $ hasPosition tp)++ "\n but got "++(show tp) )
            ((Nothing, _),            (err, _)) -> err
            ((err, _),                _) -> err


checkFunctions:: [AbsGramar.TopDef]-> Funcs -> Vars -> Err
checkFunctions [] _ _ = Nothing
checkFunctions ((FnDef _ retTyp _ args (Block _ stmts)):fT) declFunc vars = case checkFunction stmts retTyp declFunc (foldl (\a (Arg _ tp ident)->Map.insert (identToString ident) (tp,False) a) vars args) of
    Nothing -> checkFunctions fT declFunc vars
    err -> err             --(foldl (\a (Arg _ tp ident)->Map.insert (identToString ident) tp a) vars args)

check:: [AbsGramar.TopDef] -> [AbsGramar.TopDef] -> [AbsGramar.TopDef]-> (Err,[AbsGramar.TopDef],[AbsGramar.TopDef])
check p globVars funcs =
    case p of
        h:t-> case h of 
            (FnDef _ _ _ _ _) -> check t globVars (h:funcs)
            _ -> check t (h:globVars) funcs
        [] -> do
            let err = checkForDuplicates globVars Set.empty in if err == Nothing then
                (checkForDuplicates funcs Set.empty, globVars, funcs)
            else 
                (err, globVars, funcs)

addFunc:: String -> AbsGramar.Type -> AbsGramar.TopDef
addFunc sIdent tp = let nPos = BNFC'NoPosition in FnDef nPos (Int nPos) (Ident sIdent) [Arg nPos tp (Ident "arg")] (Block nPos [])

typeChecker:: [AbsGramar.TopDef] -> Err
typeChecker p = 
    case check p [] [(addFunc "printInt" (Int BNFC'NoPosition)),(addFunc "printString" (Str BNFC'NoPosition))] of
        (Nothing, vars, funcs) -> checkFunctions funcs (foldl (\a x->Map.insert (hasIdent x) x a) Map.empty funcs) (foldl (\a (GlobDecl _ tp (Init _ i _))->Map.insert (identToString i) (tp,False) a) Map.empty vars)
        (err, _, _) -> err
    