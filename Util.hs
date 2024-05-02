module Util where

-- import Prelude
--   ( ($), (.)
--   , Either(..)
--   , Int, (>)
--   , String, (++), concat, unlines
--   , Show, show
--   , IO, (>>), (>>=), mapM_, putStrLn
--   , FilePath
--   , getContents, readFile
--   )

import AbsGramar 

type Err = Maybe String

identToString i = 
    case i of
        Ident s -> s

class HasIdent a where
  hasIdent :: a -> String

instance HasIdent AbsGramar.TopDef where
  hasIdent tpDef= 
    case tpDef of
        FnDef _ _ i _ _ -> identToString i
        GlobDecl _ _ (Init _ i _) -> identToString i

showPosition mp = case mp of
    Just p -> "at line " ++ show (fst p) ++ ", and column "++ show(snd p)
    Nothing -> ""

(<=>):: AbsGramar.Type -> AbsGramar.Type -> Bool
(Int _) <=> (Int _) = True
(Str _) <=> (Str _) = True
(Bool _) <=> (Bool _) = True
_ <=> _  = False

(</>):: AbsGramar.Type -> AbsGramar.Type -> Bool
l </> r = not (l <=> r)