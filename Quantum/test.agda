module test where

open import Qio
open import Complex
open import Data.Unit
open import Data.String
open import Data.Bool
open import Data.Product
open import Data.List hiding (_++_)
import IO as IO
open import IO.Primitive

postulate
  showℝ : ℝ -> String

{-# COMPILED showℝ show :: Float -> String #-}

showℂ : ℂ -> String
showℂ (a :+ b) = showℝ a ++ " :+ " ++ showℝ b ++ "i"

showBool : Bool -> String
showBool true = "true"
showBool false = "false"

showBool× : Bool × Bool -> String
showBool× (x , y) = "( " ++ showBool x ++ " , " ++ showBool y ++ " )"

showRun : ∀{A} -> (A -> String) -> List (A × ℝ) -> String
showRun f [] = ""
showRun f ((x , y) ∷ xs) = f x ++ ":" ++ showℝ y ++ " , " ++ showRun f xs

rand' : IO.IO ⊤
rand' = IO.putStrLn ("Qio.run rand = " ++ (showRun (showBool) (Qio.run rand)))

hadTwice' : IO.IO ⊤
hadTwice' = IO.putStrLn ("Qio.run hadTwice = " ++ (showRun (showBool) (Qio.run hadTwice)))

measBell' : IO.IO ⊤
measBell' = IO.putStrLn ("Qio.run measBell = " ++ (showRun (showBool×) (Qio.run measBell)))

showF : (Bool -> Bool) -> String
showF f with f true | f false
showF f | true | true = "x -> true"
showF f | true | false = "id"
showF f | false | true = "not"
showF f | false | false = "x -> false"

deutsch' : (Bool -> Bool) -> IO.IO ⊤
deutsch' f = IO.putStrLn ("Qio.run (deustch ( " ++ (showF f) ++ " )) = " ++ (showRun (showBool) (Qio.run (deutsch f))))

teleportBool' : Bool -> IO.IO ⊤
teleportBool' b = IO.putStrLn ("Qio.run (telportBool " ++ showBool b ++ ") = " ++ (showRun (showBool) (Qio.run (teleportBool b))))

main : IO ⊤
main = IO.run rand' >>= \_ ->
       IO.run hadTwice' >>= \_ ->
       IO.run measBell' >>= \_ ->
       IO.run (deutsch' (\x -> x)) >>= \_ ->
       IO.run (deutsch' not) >>= \_ ->
       IO.run (deutsch' (\x -> true)) >>= \_ ->
       IO.run (deutsch' (\x -> false)) >>= \_ ->
       IO.run (teleportBool' false) >>= \_ ->
       IO.run (teleportBool' true)