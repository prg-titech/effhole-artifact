module Elaboration (elaborate) where 

import Common
import qualified External as E
import qualified Internal as I
import Bound

elaborate :: E.Expr -> I.Expr Id
elaborate e = elaborate' e []

elaborate' :: E.Expr -> [E.BindVar] -> I.Expr Id
elaborate' (E.Var x) _ = I.Var x
elaborate' (E.BV b) _ = I.BV b
elaborate' (E.NV n) _ = I.NV n
elaborate' (E.Str s) _ = I.Str s
elaborate' E.Unit _ = I.Unit
elaborate' (E.BiOp op e1 e2) xs = I.BiOp op (elaborate' e1 xs) (elaborate' e2 xs)
elaborate' E.Nil _ = I.Nil
elaborate' (E.Cons e1 e2) xs = I.Cons (elaborate' e1 xs) (elaborate' e2 xs)
elaborate' (E.UnCons e1 e2 id1 id2 e) xs =
  let x = E.name id1
      k = E.name id2
   in I.UnCons (elaborate' e1 xs) (elaborate' e2 xs) x k (I.abstract2 x k (elaborate' e (id1:id2:xs)))
elaborate' (E.Abs x [] e) xs = I.Abs (E.name x) (abstract1 (E.name x) (elaborate' e (x:xs)))
elaborate' (E.Abs x (y:ys) e) xs = I.Abs (E.name x) (abstract1 (E.name x) (elaborate' (E.Abs y ys e) (x:xs)))
elaborate' (E.Pair e1 e2) xs = I.Pair (elaborate' e1 xs) (elaborate' e2 xs)
elaborate' (E.InLorR b e) xs = I.InLorR b (elaborate' e xs)
elaborate' (E.UnEither e x le y re) xs =
  let lx = E.name x
      ry = E.name y
   in I.UnEither (elaborate' e xs) lx (abstract1 lx (elaborate' le (x:xs))) 
                 ry (abstract1 ry (elaborate' re (y:xs)))
elaborate' (E.Handler x e cases) xs =
  let hx = E.name x
   in I.Handler hx (abstract1 hx (elaborate' e (x:xs))) 
        [(op, (E.name caseX, E.name k, I.abstract2 (E.name caseX) (E.name k) (elaborate' case' (caseX:k:xs))))
        | E.HandlerCase op caseX k case' <- cases]
elaborate' (E.Unpair e id1 id2 e') xs =
  let x = E.name id1
      y = E.name id2
   in I.Unpair (elaborate' e xs) 
        x y (I.abstract2 x y (elaborate' e' (id1:id2:xs)))
elaborate' (E.App e1 e2) xs = I.App (elaborate' e1 xs) (elaborate' e2 xs)
elaborate' (E.If e1 e2 e3) xs = I.If (elaborate' e1 xs) (elaborate' e2 xs) (elaborate' e3 xs)
elaborate' (E.OpCall op e) xs = I.OpCall (elaborateOp op) (elaborate' e xs)
  where
    elaborateOp (E.Operation arithOp) = I.Operation arithOp
    elaborateOp (E.OpHole i) = I.OpHole i
elaborate' (E.With e1 e2) xs = I.With (elaborate' e1 xs) (elaborate' e2 xs)
elaborate' (E.Do [] r) xs = elaborate' r xs
elaborate' (E.Do ((E.DoExpr e):es) r) xs = I.Do (elaborate' e xs) dummy (abstract1 dummy (elaborate' (E.Do es r) xs))
elaborate' (E.Do ((E.DoBind x e):es) r) xs =
  let bx = E.name x
   in I.Do (elaborate' e xs) bx (abstract1 bx (elaborate' (E.Do es r) (x:xs)))
elaborate' (E.Do ((E.LetRec f x [] e):es) r) xs =
  let ff = E.name f
      xx = E.name x
   in I.LetRec ff xx (I.abstract2 ff xx (elaborate' e (f:x:xs))) 
        (abstract1 ff (elaborate' (E.Do es r) (f:xs)))
elaborate' (E.Do ((E.LetRec f x (y:ys) e):es) r) xs =
  let ff = E.name f
      xx = E.name x
   in I.LetRec ff xx (I.abstract2 ff xx (elaborate' (E.Abs y ys e) (f:x:xs))) 
        (abstract1 ff (elaborate' (E.Do es r) (f:xs)))
elaborate' (E.ExprHole i) xs = I.ExprHole i Nothing [ (x, I.Var (E.name x)) | x <- dedupe xs ]
  where
    dedupe :: [E.BindVar] -> [E.BindVar]
    dedupe = go []
      where
        go seen [] = reverse seen
        go seen (x:rest)
          | E.name x `elem` map E.name seen = go seen rest
          | otherwise = go (x:seen) rest
